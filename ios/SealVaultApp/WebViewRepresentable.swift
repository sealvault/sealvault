// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation
import SwiftUI
import WebKit

/**
 Bridge WKWebView from UIKit to SwiftUI.
 */
public struct WebViewRepresentable: UIViewRepresentable {
    var stateModel: BrowserModel

    let scriptHandler: WebViewScriptHandler

    init(core: AppCoreProtocol, stateModel: BrowserModel) {
        self.stateModel = stateModel

        scriptHandler = WebViewScriptHandler(core: core, stateModel: stateModel)
    }

    // TODO: deinit: https://stackoverflow.com/a/65270084/2650622
    // TODO: https://stackoverflow.com/questions/26383031/wkwebview-causes-my-view-controller-to-leak
    public func makeUIView(context: Context) -> WKWebView {
        let webViewConfiguration = WKWebViewConfiguration()

        if ProcessInfo.processInfo.environment["XCODE_RUNNING_FOR_PREVIEWS"] != "1" {
            if let scriptSource = scriptHandler.getInPageScript() {
                let userScript = WKUserScript(
                    source: scriptSource, injectionTime: .atDocumentStart, forMainFrameOnly: false
                )

                let contentController = WKUserContentController()
                contentController.addUserScript(userScript)
                contentController.addScriptMessageHandler(
                    scriptHandler, contentWorld: .page, name: scriptHandler.handlerName
                )

                webViewConfiguration.userContentController = contentController
            }
        } else {
            print("Skipping in-page provider script as the app core isn't initialized in preview mode")
        }

        // Private browsing (stores data in memory, gone on app restart)
        webViewConfiguration.websiteDataStore = WKWebsiteDataStore.nonPersistent()
        webViewConfiguration.upgradeKnownHostsToHTTPS = true

        let webView = WKWebView(frame: CGRect.zero, configuration: webViewConfiguration)
        webView.navigationDelegate = context.coordinator
        webView.uiDelegate = context.coordinator
        webView.scrollView.delegate = context.coordinator
        scriptHandler.webView = webView

        // Pull down to refresh
        let refreshControl = UIRefreshControl()
        refreshControl.addTarget(webView, action: #selector(WKWebView.reloadForRefresh(_:)), for: .valueChanged)
        webView.scrollView.bounces = true
        webView.scrollView.addSubview(refreshControl)

        // Let us inspect WKWebView with Safari dev tools
#if DEBUG
        webView.configuration.preferences.setValue(true, forKey: "developerExtrasEnabled")
#endif

        loadUrlIfValid(webView: webView)

        return webView
    }

    public func updateUIView(_ webView: WKWebView, context _: Context) {
        DispatchQueue.main.async {
            let model = self.stateModel
            if model.urlChanged {
                loadUrlIfValid(webView: webView)
                // Important to set to false even if the url is invalid,
                // bc the semantics is that we tried to process the change.
                model.urlChanged = false
            } else if webView.canGoBack, model.goBack {
                webView.goBack()
                model.goBack = false
            } else if webView.canGoForward, model.goForward {
                webView.goForward()
                model.goForward = false
            }
        }
    }

    public func makeCoordinator() -> Coordinator {
        Coordinator(stateModel: stateModel)
    }

    public final class Coordinator: NSObject {
        var stateModel: BrowserModel

        init(stateModel: BrowserModel) {
            self.stateModel = stateModel
        }
    }

    func loadUrlIfValid(webView: WKWebView) {
        if let url = stateModel.url {
            webView.load(URLRequest(url: url))
        }
    }
}

extension WKWebView {
    @objc func reloadForRefresh(_ sender: UIRefreshControl) {
        defer {
            sender.endRefreshing()
        }
        // TODO: if initial load failed self.url == nil and reload
        // will have no effect. have to pass the desired url somehow for refresh
        reload()
    }
}

final class WebViewScriptHandler: NSObject, WKScriptMessageHandlerWithReply {
    let core: AppCoreProtocol
    let stateModel: BrowserModel

    let handlerName: String = "sealVaultRequestHandler"
    let handlerKey: String
    let rpcProviderName: String = "_sealVaultRpcProvider"

    // TODO: rethink hierarchy to avoid weak reference
    weak var webView: WKWebView?

    init(core: AppCoreProtocol, stateModel: BrowserModel) {
        self.core = core
        self.stateModel = stateModel
        handlerKey = "webkit.messageHandlers.\(handlerName).postMessage"

        super.init()
    }

    func getInPageScript() -> String? {
        do {
            return try core.getInPageScript(rpcProviderName: rpcProviderName, requestHandlerName: handlerKey)
        } catch {
            print("Error getting in page script: \(error)")
            return nil
        }
    }

    func userContentController(
        _: WKUserContentController, didReceive message: WKScriptMessage,
        replyHandler: @escaping (Any?, String?) -> Void
    ) {
        if UIApplication.shared.applicationState == .background {
            return
        }
        if message.name == handlerName {
            guard let context = InPageRequestContext.build(stateModel, message, rpcProviderName: rpcProviderName) else {
                return
            }
            guard let messageBody = message.body as? String else {
                return
            }

            DispatchQueue.global(qos: .background).async { [weak self] in
                do {
                    let response = try self?.core.inPageRequest(context: context, rawRequest: messageBody)
                    // TODO: what happens if page navigates away before we reply?
                    DispatchQueue.main.async {
                        replyHandler(response, nil)
                    }
                } catch {
                    if let err = error as? CoreError {
                        print("Core error resolving in page request: \(err) for message \(messageBody)")
                        DispatchQueue.main.async {
                            replyHandler(nil, "Core error")
                        }
                    } else {
                        print("Unknown error resolving in page request: \(error) for message \(messageBody)")
                        DispatchQueue.main.async {
                            replyHandler(nil, "Unknown error")
                        }
                    }
                }
            }
        } else {
            print("unknown message recipient: \(message.name)")
        }
    }
}

class InPageRequestContext: InPageRequestContextI {
    var stateModel: BrowserModel
    var message: WKScriptMessage
    var webViewUrl: URL
    var rpcProviderName: String

    init(_ stateModel: BrowserModel, _ message: WKScriptMessage, _ webViewUrl: URL, rpcProviderName: String) {
        self.stateModel = stateModel
        self.message = message
        self.webViewUrl = webViewUrl
        self.rpcProviderName = rpcProviderName
    }

    static func build(
        _ stateModel: BrowserModel, _ message: WKScriptMessage, rpcProviderName: String
    ) -> InPageRequestContext? {
        guard let webView = message.webView else {
            return nil
        }
        guard let url = webView.url else {
            return nil
        }
        return InPageRequestContext(stateModel, message, url, rpcProviderName: rpcProviderName)
    }

    func pageUrl() -> String {
        webViewUrl.absoluteString
    }

    func callbacks() -> CoreInPageCallbackI {
        CoreInPageCallback(stateModel, message, rpcProviderName: rpcProviderName)
    }
}

// The callbacks are dispatched on a background thread from `userContentController`
class CoreInPageCallback: CoreInPageCallbackI {
    var stateModel: BrowserModel
    var message: WKScriptMessage
    var rpcProviderName: String

    init(_ stateModel: BrowserModel, _ message: WKScriptMessage, rpcProviderName: String) {
        self.stateModel = stateModel
        self.message = message
        self.rpcProviderName = rpcProviderName
    }

    func approveDapp(dappApproval: DappApprovalParams) -> Bool {
        var approved = false
        let semaphore = DispatchSemaphore(value: 0)
        let request = DappApprovalRequest(
            accountId: dappApproval.accountId,
            dappHumanIdentifier: dappApproval.dappIdentifier,
            dappFavicon: dappApproval.favicon,
            // These callbacks are called on the UI thread
            approve: {
                approved = true
                semaphore.signal()
            },
            dismiss: {
                semaphore.signal()
            }
        )

        DispatchQueue.main.async { [weak self] in
            guard let that = self else {
                return
            }
            that.stateModel.dappApprovalRequest = request
        }

        // TODO should we add timeout? We'd have to be able to dismiss the modal though
        // if it times out which we can't as is
        semaphore.wait()
        return approved
    }

    func notify(messageHex: String) {
        DispatchQueue.main.async {
            // Must capture self to prevent the callback object from being GCed before this has a chance to run
            guard let webView = self.message.webView else {
                print("Returning early from notify: webview has been GCed")
                return
            }

            webView.evaluateJavaScript("window.\(self.rpcProviderName).notify('\(messageHex)')")
        }
    }
}

// TODO: implement all WKNavigationDelegate methods
extension WebViewRepresentable.Coordinator: WKNavigationDelegate {
    public func webView(_: WKWebView, didStartProvisionalNavigation _: WKNavigation!) {
        stateModel.requestStatus = "Loading page..."
        stateModel.loading = true
    }

    public func webView(
        _ webView: WKWebView,
        didFailProvisionalNavigation _: WKNavigation!,
        withError error: Error
    ) {
        // Blocked http navigation, upgrade to https
        if error._domain == "NSURLErrorDomain", error._code == -1022 {
            if let info = error._userInfo as? [String: Any] {
                if let url = info["NSErrorFailingURLKey"] as? URL {
                    let components = NSURLComponents(url: url, resolvingAgainstBaseURL: true)!
                    components.scheme = "https"
                    stateModel.addressBarText = components.url!.absoluteString
                    stateModel.urlChanged = true
                }
            }
        } else {
            print("didFailProvisionalNavigation: \(error)")
            stateModel.requestStatus = "Failed to load page"
            stateModel.loading = false
            stateModel.canGoBack = webView.canGoBack
            stateModel.canGoForward = webView.canGoForward
        }
    }

    public func webView(_ webView: WKWebView, didFinish _: WKNavigation!) {
        stateModel.loading = false
        stateModel.canGoBack = webView.canGoBack
        stateModel.canGoForward = webView.canGoForward
        if let url = webView.url {
            stateModel.addressBarText = url.absoluteString
        }
        stateModel.requestStatus = nil
    }

    public func webView(
        _ webView: WKWebView,
        didFail _: WKNavigation!,
        withError error: Error
    ) {
        print("didFail: \(error)")
        stateModel.requestStatus = "Failed to load page"
        stateModel.loading = false
        stateModel.canGoBack = webView.canGoBack
        stateModel.canGoForward = webView.canGoForward
    }
}

extension WebViewRepresentable.Coordinator: WKUIDelegate {
    // Open new tab in same view
    // https://stackoverflow.com/a/41116379/2650622
    public func webView(
        _: WKWebView, createWebViewWith _: WKWebViewConfiguration, for navigationAction: WKNavigationAction,
        windowFeatures _: WKWindowFeatures)
    -> WKWebView? {
        if navigationAction.targetFrame == nil {
            if let url = navigationAction.request.url {
                stateModel.addressBarText = url.absoluteString
                stateModel.urlChanged = true
            }
        }
        return nil
    }
}

extension WebViewRepresentable.Coordinator: UIScrollViewDelegate {
    public func scrollViewDidScroll(_ scrollView: UIScrollView) {
        // This is dispatched to get around this issue: https://developer.apple.com/forums/thread/711899
        DispatchQueue.main.async { [weak self] in
            let yCoord = scrollView.panGestureRecognizer.translation(in: scrollView.superview).y
            withAnimation {
                // Margins are there to avoid hiding on simple tap by accident
                if yCoord > 0.1 {
                    self?.stateModel.navHidden = false
                } else if yCoord < -0.1 {
                    self?.stateModel.navHidden = true
                }
            }
        }
    }
}
