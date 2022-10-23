// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

class BrowserModel: ObservableObject {
    @Published var urlRaw: String
    @Published var addressBarText: String
    @Published var doLoad: Bool = false
    @Published var doReload: Bool = false
    @Published var doStop: Bool = false
    @Published var loading: Bool = false
    @Published var canGoBack: Bool = false
    @Published var goBack: Bool = false
    @Published var canGoForward: Bool = false
    @Published var goForward: Bool = false
    @Published var dappApprovalRequest: DappApprovalRequest?
    @Published var dappApprovalPresented = false
    @Published var loadingProgress: Double = 0.0

    init(homePage: String) {
        self.urlRaw = homePage
        self.addressBarText = homePage
    }

    var url: URL? {
        URL(string: urlRaw.trimmingCharacters(in: NSCharacterSet.whitespacesAndNewlines))
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

    func setRawUrl(_ url: URL?) {
        // File is used for the error page
        if let url = url, url.scheme != "file" {
            self.urlRaw = url.absoluteString
        }
    }

    @MainActor
    func setDappApproval(_ request: DappApprovalRequest?) {
        if let req = request {
            self.dappApprovalRequest = req
            self.dappApprovalPresented = true
        } else {
            self.dappApprovalRequest = nil
            self.dappApprovalPresented = false

        }
    }
}

struct BrowserView: View {
    @EnvironmentObject private var viewModel: GlobalModel
    @StateObject var browserModel: BrowserModel

    var body: some View {
        BrowserViewInner(core: viewModel.core, browserModel: browserModel)
        .sheet(isPresented: $browserModel.dappApprovalPresented) {
            DappApproval(request: browserModel.dappApprovalRequest!)
                .presentationDetents([.medium])
                .background(.ultraThinMaterial)
        }
    }
}

struct BrowserViewInner: View {
    let core: AppCoreProtocol
    @ObservedObject var browserModel: BrowserModel
    var body: some View {
        VStack(spacing: 0) {
            WebViewRepresentable(core: core, model: browserModel)
            AddressBar(browserModel: browserModel)
        }
    }
}

struct AddressBar: View {
    @ObservedObject var browserModel: BrowserModel
    @FocusState private var isAddressBarFocused: Bool
    @State private var showProgressView: Bool = false

    var body: some View {
        HStack {
            HStack {
                Button(action: {
                    browserModel.goBack = true
                }, label: {
                    Image(systemName: "arrow.left")
                })
                .disabled(!browserModel.canGoBack)

                if browserModel.canGoForward {
                    Button(action: {
                        browserModel.goForward = true
                    }, label: {
                        Image(systemName: "arrow.right")
                    })
                }
            }.padding(.horizontal, 5)
            ZStack(alignment: .bottom) {
                TextField("url / search", text: $browserModel.addressBarText)
                    .textInputAutocapitalization(.never)
                    .disableAutocorrection(true)
                    .accessibility(identifier: "browserAddressBar")
                    .multilineTextAlignment(.center)
                    .textFieldStyle(.roundedBorder)
                    .focused($isAddressBarFocused)
                    .onSubmit {
                        if let url = uriFixup(input: browserModel.addressBarText) {
                            browserModel.urlRaw = url
                            browserModel.doLoad = true
                        } else if let searchUrl = browserModel.searchUrl() {
                            browserModel.urlRaw = searchUrl.absoluteString
                            browserModel.doLoad = true
                        } else {
                            print("Unexpected: invalid url and search url \(browserModel.urlRaw)")
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
                if showProgressView {
                    ProgressView(value: browserModel.loadingProgress)
                        // Make the bar thinner
                        .scaleEffect(x: 1, y: 0.5, anchor: .center)
                }
            }
            HStack {
                if browserModel.loading {
                    Button(action: {
                        browserModel.doStop = true
                    }, label: {
                        Image(systemName: "xmark")
                    })
                } else {
                    Button(action: {
                        browserModel.doReload = true
                    }, label: {
                        Image(systemName: "arrow.clockwise")
                    })
                }
            }
            .padding(.horizontal, 5)
        }
        .padding(10)
        .onChange(of: browserModel.urlRaw) { newQuery in
            if !isAddressBarFocused {
                browserModel.addressBarText = newQuery
            }
        }
        .onChange(of: browserModel.loading) { newValue in
            if newValue {
                // Show progress bar immediately on start
                withAnimation {
                    showProgressView = newValue
                }
            } else {
                // Delay hiding progress bar after success, otherwise it's not allowed to complete
                DispatchQueue.main.asyncAfter(deadline: .now() + 1) {
                    withAnimation {
                        showProgressView = newValue
                    }
                }
            }
        }
    }
}

#if DEBUG
struct WebView_Previews: PreviewProvider {
    static var previews: some View {
        var browserModel = BrowserModel(homePage: Config.browserOneHomePage)
        BrowserView(browserModel: browserModel).environmentObject(GlobalModel.buildForPreview())
    }
}
#endif
