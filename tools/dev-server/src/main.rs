// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use std::{fs::File, io::Read, path::PathBuf, sync::Arc};

use actix_files as fs;
use actix_web::{
    get, http::header, middleware::Logger, post, web, App, HttpRequest, HttpResponse,
    HttpServer, Responder,
};
use dotenv::dotenv;
use ethers_core::utils::hex;
use uniffi_sealvault_core::{
    AppCore, CoreArgs, CoreInPageCallbackI, CoreUICallbackI, DappAllotmentTransferResult,
    DappApprovalParams, DappSignatureResult, DappTransactionResult, DappTransactionSent,
    InPageRequestContextI,
};

const DB_PATH: &str = ":memory:";
const STATIC_FOLDER: &str = "./static";

/// SealVault Dev Server
///
/// Serves the static directory at `http://localhost:8080/` and proxies requests to the backend
/// at http://localhost:8080/backend
///
#[actix_web::main]
async fn main() -> std::io::Result<()> {
    dotenv().ok();

    env_logger::init_from_env(env_logger::Env::new().default_filter_or("info"));

    let backend_args = CoreArgs {
        cache_dir: "./cache".into(),
        db_file_path: DB_PATH.into(),
    };
    let backend_service = Arc::new(
        AppCore::new(backend_args, Box::new(CoreUICallBackMock::new()))
            .expect("core initializes"),
    );

    HttpServer::new(move || {
        App::new()
            .wrap(Logger::default())
            .app_data(web::Data::new(backend_service.clone()))
            .service(in_page_provider)
            .service(get_html)
            .service(backend)
            .service(fs::Files::new("/", STATIC_FOLDER).index_file("index.html"))
    })
    .bind(("127.0.0.1", 8080))?
    .run()
    .await
}

#[post("/backend")]
async fn backend(
    backend_service: web::Data<Arc<AppCore>>,
    req: HttpRequest,
    req_body: String,
) -> impl Responder {
    let default_referer: header::HeaderValue = header::HeaderValue::from_str("").unwrap();
    let referer = req
        .headers()
        .get("Referer")
        .unwrap_or(&default_referer)
        .to_str()
        .unwrap();
    // TODO support respond and notify
    let iprc = Box::new(InPageRequestContextMock::new(referer));
    let result = tokio::task::spawn_blocking(move || {
        backend_service.in_page_request(iprc, req_body)
    })
    .await
    .expect("thread can be joined");
    match result {
        Ok(body) => HttpResponse::Ok().body(body),
        Err(err) => HttpResponse::InternalServerError().body(err.to_string()),
    }
}

#[get("/{html_path}.html")]
async fn get_html(req: HttpRequest) -> impl Responder {
    let default_user_agent: header::HeaderValue =
        header::HeaderValue::from_str("none").unwrap();
    let user_agent = req
        .headers()
        .get("User-Agent")
        .unwrap_or(&default_user_agent)
        .to_str()
        .unwrap()
        .to_lowercase();

    let mut file_path = PathBuf::from(STATIC_FOLDER);
    let filename: PathBuf = req.match_info().get("html_path").unwrap().parse().unwrap();
    file_path.push(filename);
    file_path.set_extension("html");
    match File::open(&file_path) {
        Ok(mut file) => {
            let mut contents = String::new();
            file.read_to_string(&mut contents).unwrap();
            if !user_agent.contains("iphone") {
                contents = contents.replace("<!--desktop-only", "");
                contents = contents.replace("desktop-only-->", "");
            }
            HttpResponse::Ok().content_type("text/html").body(contents)
        }
        Err(_) => {
            HttpResponse::NotFound().body(format!("Not found: {}", file_path.display()))
        }
    }
}

#[get("/js/in-page-provider.js")]
async fn in_page_provider(backend_service: web::Data<Arc<AppCore>>) -> impl Responder {
    const SEALVAULT_RPC_PROVIDER: &str = "sealVaultRpcProvider";
    const SEALVAULT_REQUEST_HANDLER: &str = "sealVaultRequestHandler";

    let contents = backend_service
        .get_ref()
        .get_in_page_script(
            SEALVAULT_RPC_PROVIDER.into(),
            SEALVAULT_REQUEST_HANDLER.into(),
        )
        .unwrap();

    HttpResponse::Ok()
        .content_type("application/javascript")
        .body(contents)
}

#[derive(Debug, Default)]
pub struct CoreUICallBackMock {}

impl CoreUICallBackMock {
    pub fn new() -> Self {
        Self {}
    }
}

impl CoreUICallbackI for CoreUICallBackMock {
    fn dapp_allotment_transfer_result(&self, result: DappAllotmentTransferResult) {
        log::info!("Dapp allotment transfer result: {:?}", result)
    }

    fn signed_message_for_dapp(&self, result: DappSignatureResult) {
        log::info!("Dapp signature result: {:?}", result)
    }

    fn sent_transaction_for_dapp(&self, result: DappTransactionSent) {
        log::info!("Sent transactions for dapp result: {:?}", result)
    }

    fn dapp_transaction_result(&self, result: DappTransactionResult) {
        log::info!("Dapp transaction result: {:?}", result)
    }
}

#[derive(Debug)]
pub struct InPageRequestContextMock {
    pub page_url: String,
    pub callbacks: Box<CoreInPageCallbackMock>,
}

impl InPageRequestContextMock {
    pub fn new(page_url: &str) -> Self {
        Self {
            page_url: page_url.into(),
            callbacks: Box::new(CoreInPageCallbackMock::new()),
        }
    }
    pub fn default_boxed() -> Box<Self> {
        Box::new(InPageRequestContextMock::new("https://example.com"))
    }
}

impl InPageRequestContextI for InPageRequestContextMock {
    fn page_url(&self) -> String {
        self.page_url.clone()
    }

    fn callbacks(&self) -> Box<dyn CoreInPageCallbackI> {
        self.callbacks.clone()
    }
}

#[derive(Debug, Clone)]
pub struct CoreInPageCallbackMock {}

impl CoreInPageCallbackMock {
    // We don't want to create the mock by accident with `Default::default`.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self {}
    }
}

impl CoreInPageCallbackI for CoreInPageCallbackMock {
    fn request_dapp_approval(&self, _: DappApprovalParams) {
        // Don't slow down tests noticeably, but simulate blocking.
        std::thread::sleep(std::time::Duration::from_millis(1));
    }

    fn respond(&self, response_hex: String) {
        let response = hex::decode(response_hex).expect("valid hex");
        let response = String::from_utf8_lossy(&response);
        log::info!("CoreInPageCallbackMock.response: '{:?}'", response);
    }

    fn notify(&self, message_hex: String) {
        let event = hex::decode(message_hex).expect("valid hex");
        let event = String::from_utf8_lossy(&event);
        log::info!("CoreInPageCallbackMock.notify: '{:?}'", event);
    }
}
