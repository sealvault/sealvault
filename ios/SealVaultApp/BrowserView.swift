// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

class BrowserModel: ObservableObject {
    @Published var urlRaw: String = Config.defaultHomePage
    @Published var addressBarText: String = Config.defaultHomePage
    @Published var loadUrl: Bool = false
    @Published var requestStatus: String? = "Loading..."
    @Published var loading: Bool = false
    @Published var canGoBack: Bool = false
    @Published var goBack: Bool = false
    @Published var canGoForward: Bool = false
    @Published var goForward: Bool = false
    @Published var dappApprovalRequest: DappApprovalRequest?
    @Published var dappApprovalPresented = false

    var url: URL? {
        URL(string: urlRaw.trimmingCharacters(in: NSCharacterSet.whitespacesAndNewlines))
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

    @MainActor
    func setDappApproval(_ request: DappApprovalRequest?) {
        if let req = request {
            self.dappApprovalRequest = request
            self.dappApprovalPresented = true
        } else {
            self.dappApprovalRequest = nil
            self.dappApprovalPresented = false

        }
    }
}

struct BrowserView: View {
    @EnvironmentObject private var viewModel: GlobalModel
    @StateObject var browserModel = BrowserModel()

    var body: some View {
        BrowserViewInner(core: viewModel.core, browserModel: browserModel)
        .sheet(isPresented: $browserModel.dappApprovalPresented) {
            DappApproval(request: browserModel.dappApprovalRequest!)
                .presentationDetents([.medium])
                .background(.ultraThinMaterial)
        }
        .navigationBarTitleDisplayMode(.inline)
        .navigationTitle(browserModel.navTitle)
        .toolbar {
            ToolbarItem(placement: ToolbarItemPlacement.navigationBarLeading) {
                if browserModel.loading {
                    ProgressView()
                        .progressViewStyle(CircularProgressViewStyle())
                } else {
                    Button {
                        browserModel.loadUrl = true
                    } label: {
                        Image(systemName: "arrow.counterclockwise")
                    }

                }
            }
            ToolbarItem(placement: .navigationBarTrailing) {
                if let activeAccount = viewModel.activeAccount {
                    AccountImageCircle(account: activeAccount)
                }
            }
        }

    }
}

struct BrowserViewInner: View {
    let core: AppCoreProtocol
    @ObservedObject var browserModel: BrowserModel
    @FocusState private var isAddressBarFocused: Bool

    var body: some View {
        VStack(spacing: 0) {
            WebViewRepresentable(core: core, stateModel: browserModel)

            HStack {
                Button(action: {
                    browserModel.goBack = true
                }, label: {
                    Image(systemName: "arrow.left")
                })
                .disabled(!browserModel.canGoBack)
                .padding(.horizontal, 5)
                TextField("url / search", text: $browserModel.addressBarText)
                    .textInputAutocapitalization(.never)
                    .disableAutocorrection(true)
                    .accessibility(identifier: "browserAddressBar")
                    .multilineTextAlignment(.center)
                    .textFieldStyle(.roundedBorder)
                    .padding(.horizontal, 5)
                    .focused($isAddressBarFocused)
                    .onSubmit {
                        if let url = uriFixup(input: browserModel.addressBarText) {
                            browserModel.urlRaw = url
                            browserModel.loadUrl = true
                        } else if let searchUrl = browserModel.searchUrl() {
                            browserModel.urlRaw = searchUrl.absoluteString
                            browserModel.loadUrl = true
                        } else {
                            print("Unexpected: invalid url and search url \(browserModel.urlRaw)")
                        }
                    }
                    .onChange(of: browserModel.urlRaw) { newQuery in
                        if !isAddressBarFocused {
                            browserModel.addressBarText = newQuery
                        }
                    }
                    .onReceive(NotificationCenter.default.publisher(
                        for: UITextField.textDidBeginEditingNotification
                    )) { obj in
                        // Select text field on tap
                        if let textField = obj.object as? UITextField {
                            textField.selectedTextRange = textField.textRange(
                                from: textField.beginningOfDocument, to: textField.endOfDocument
                            )
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

#if DEBUG
struct WebView_Previews: PreviewProvider {
    static var previews: some View {
        BrowserView().environmentObject(GlobalModel.buildForPreview())
    }
}
#endif
