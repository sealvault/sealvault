// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

class BrowserModel: ObservableObject {
    @Published var addressBarText: String = Config.defaultHomePage
    @Published var urlChanged: Bool = false
    @Published var requestStatus: String? = "Loading..."
    @Published var loading: Bool = false
    @Published var canGoBack: Bool = false
    @Published var goBack: Bool = false
    @Published var canGoForward: Bool = false
    @Published var goForward: Bool = false
    @Published var navHidden: Bool = false
    @Published var dappApprovalRequest: DappApprovalRequest?

    var url: URL? {
        URL(string: addressBarText.trimmingCharacters(in: NSCharacterSet.whitespacesAndNewlines))
    }

    var navTitle: String {
        if let status = requestStatus {
            return status
        } else if let host = url?.host {
            return host
        } else {
            return ""
        }
    }

    var urlValid: Bool {
        url != nil
    }

    func searchUrl() -> URL? {
        if var urlComps = URLComponents(url: Config.searchProvider, resolvingAgainstBaseURL: false) {
            urlComps.queryItems = [URLQueryItem(name: Config.searchQueryParamName, value: addressBarText)]
            return urlComps.url
        } else {
            return nil
        }
    }
}

struct BrowserView: View {
    @EnvironmentObject private var viewModel: GlobalModel
    @StateObject var browserModel = BrowserModel()

    var body: some View {
        BrowserViewInner(core: viewModel.core, browserModel: browserModel)
        .sheet(item: $browserModel.dappApprovalRequest) { request in
            DappApproval(request: request)
                .presentationDetents([.medium])
                .background(.ultraThinMaterial)
        }
        .navigationBarTitleDisplayMode(.inline)
        .navigationTitle(browserModel.navTitle)
        .toolbar {
            ToolbarItem(placement: .navigationBarTrailing) {
                AccountImageCircle(account: viewModel.activeAccount)
            }
        }

    }
}

struct BrowserViewInner: View {
    let core: AppCoreProtocol
    @ObservedObject var browserModel: BrowserModel

    var body: some View {
        VStack(spacing: 0) {
            WebViewRepresentable(core: core, stateModel: browserModel)

            if !browserModel.navHidden || (browserModel.requestStatus != nil) {
                HStack {
                    Button(action: {
                        browserModel.goBack = true
                    }, label: {
                        Image(systemName: "arrow.left")
                    })
                    .disabled(!browserModel.canGoBack)
                    .padding(.horizontal, 5)
                    TextField("url / search", text: $browserModel.addressBarText)
                        .keyboardType(.URL)
                        .textContentType(.URL)
                        .textInputAutocapitalization(.never)
                        .disableAutocorrection(true)
                        .accessibility(identifier: "browserAddressBar")
                        .multilineTextAlignment(.center)
                        .textFieldStyle(.roundedBorder)
                        .padding(.horizontal, 5)
                        .onSubmit {
                            if let url = uriFixup(input: browserModel.addressBarText) {
                                browserModel.addressBarText = url
                                browserModel.urlChanged = true
                            } else if let searchUrl = browserModel.searchUrl() {
                                browserModel.addressBarText = searchUrl.absoluteString
                                browserModel.urlChanged = true
                            } else {
                                print("Unexpected: invalid url and search url \(browserModel.addressBarText)")
                            }
                        }
                    Button(action: {
                        browserModel.goForward = true
                    }, label: {
                        Image(systemName: "arrow.right")
                    })
                    .disabled(!browserModel.canGoForward)
                    .padding(.horizontal, 5)
                }
                .padding(10)
                // TODO this should match nav tab's background color
//                .background(Color(UIColor.quaternarySystemFill))
            }
        }
    }
}

#if DEBUG
struct WebView_Previews: PreviewProvider {
    static var previews: some View {
        BrowserView().environmentObject(GlobalModel.buildForPreview())
    }
}
#endif
