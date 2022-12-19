// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

class BrowserModel: ObservableObject {
    @Published fileprivate var urlRaw: String?
    @Published var addressBarText: String = ""
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
    @Published var isAddressBarFocused = false

    var url: URL? {
        if let url = urlRaw {
            return URL(string: url.trimmingCharacters(in: NSCharacterSet.whitespacesAndNewlines))
        } else {
            return nil
        }
    }

    var urlValid: Bool {
        url != nil
    }

    var showTopDapps: Bool {
        isAddressBarFocused || addressBarText == ""
    }

    var navigationTitle: String {
        showTopDapps ? "Top Dapps" : ""
    }

    func searchUrl() -> URL? {
        if var urlComps = URLComponents(url: Config.searchProvider, resolvingAgainstBaseURL: false) {
            urlComps.queryItems = [URLQueryItem(name: Config.searchQueryParamName, value: addressBarText)]
            return urlComps.url
        } else {
            return nil
        }
    }

    func loadRawUrl(_ rawUrl: String) {
        if let url = URL(string: rawUrl) {
            loadUrl(url)
        }
    }

    func loadUrl(_ url: URL) {
        self.setRawUrl(url)
        self.doLoad = true
    }

    func setRawUrl(_ url: URL?) {
        // File is used for the error page
        if let url = url, url.scheme != "file" {
            self.urlRaw = url.absoluteString
            if url.absoluteString != self.addressBarText {
                self.addressBarText = url.absoluteString
            }
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
            ZStack {
                WebViewRepresentable(core: core, model: browserModel)
                if browserModel.showTopDapps {
                    TopDapps(browserModel: browserModel)
                }
            }
            AddressBar(browserModel: browserModel)
        }
        .navigationTitle(browserModel.navigationTitle)
        .navigationBarTitleDisplayMode(.large)
    }
}

struct TopDapps: View {
    @ObservedObject var browserModel: BrowserModel
    @EnvironmentObject private var viewModel: GlobalModel
    @Environment(\.colorScheme) private var colorScheme

    var body: some View {
        VStack {
            List {
                ForEach(viewModel.topDapps) { dapp in
                    Button(action: {
                        if let url = dapp.url {
                            browserModel.loadUrl(url)
                        }
                        browserModel.isAddressBarFocused = false
                    }, label: {
                        DappRow(dapp: dapp)
                            .accessibilityIdentifier(dapp.displayName)
                    })
                }
            }
            .scrollDisabled(true)
        }
        .background(viewModel.tabBarColor(colorScheme))
        // Swipe up to dismiss keyboard
        .gesture(DragGesture(minimumDistance: 10, coordinateSpace: .global)
            .onEnded { value in
                if value.translation.height < 0 {
                    browserModel.isAddressBarFocused = false
                }
            })
        .task {
            // Refresh top dapps
            await viewModel.refreshProfiles()
        }
    }
}

struct AddressBar: View {
    @EnvironmentObject private var viewModel: GlobalModel
    @ObservedObject var browserModel: BrowserModel
    @FocusState private var isAddressBarFocused: Bool
    @State private var showProgressView: Bool = false

    @Environment(\.colorScheme) private var colorScheme

    var backgroundColor: Color {
        if colorScheme == .dark {
            return isAddressBarFocused ? Color(.systemGray4) : Color(.systemGray6)
        } else {
            return Color.white
        }
    }

    var body: some View {
        ZStack(alignment: .bottom) {
            HStack {
                if !isAddressBarFocused {
                    HStack {
                        HStack {
                            Button(action: {
                                browserModel.goBack = true
                            }, label: {
                                Image(systemName: "arrow.left")
                            })
                            .disabled(!browserModel.canGoBack)
                            .accessibilityIdentifier("Go back")

                            if browserModel.canGoForward {
                                Button(action: {
                                    browserModel.goForward = true
                                }, label: {
                                    Image(systemName: "arrow.right")
                                })
                                .accessibilityIdentifier("Go forward")
                            }
                        }
                        .padding(.leading, 5)
                    }

                }
                TextField("Search or enter website name", text: $browserModel.addressBarText)
                    .textInputAutocapitalization(.never)
                    .disableAutocorrection(true)
                    .accessibility(identifier: "browserAddressBar")
                    .multilineTextAlignment(.center)
                    .focused($isAddressBarFocused)
                    .onSubmit {
                        if let url = uriFixup(input: browserModel.addressBarText) {
                            browserModel.loadRawUrl(url)
                        } else if let searchUrl = browserModel.searchUrl() {
                            browserModel.loadRawUrl(searchUrl.absoluteString)
                        } else {
                            print(
                                "Unexpected: invalid url and search url \(String(describing: browserModel.urlRaw))")
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

                if !isAddressBarFocused {
                    HStack {
                        if browserModel.loading {
                            Button(action: {
                                browserModel.doStop = true
                            }, label: {
                                Image(systemName: "xmark")
                            })
                            .accessibilityIdentifier("Stop loading")
                        } else {
                            Button(action: {
                                browserModel.doReload = true
                            }, label: {
                                Image(systemName: "arrow.clockwise")
                            })
                            .disabled(!browserModel.urlValid)
                            .accessibilityIdentifier("Reload page")
                        }
                    }
                    .padding(.trailing, 5)
                }
            }
            .padding(10)
            .background((RoundedRectangle(cornerRadius: 10)).fill(backgroundColor))
            .clipped()
            .shadow(radius: 2)
            .padding(.horizontal, 20)
            .padding(.vertical, 10)
            .background(viewModel.tabBarColor(colorScheme))

            if showProgressView {
                ProgressView(value: browserModel.loadingProgress)
                    .scaleEffect(x: 1, y: 0.5, anchor: .center)
                    .padding(.horizontal, 28)
                    .offset(y: -8)
            }

        }
        .onChange(of: isAddressBarFocused) { newValue in
            browserModel.isAddressBarFocused = newValue
            if !browserModel.isAddressBarFocused && browserModel.urlRaw != browserModel.addressBarText {
                browserModel.addressBarText = browserModel.urlRaw ?? ""
            }
        }
        .onChange(of: browserModel.isAddressBarFocused) { newValue in
            if newValue != isAddressBarFocused {
                isAddressBarFocused = newValue
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
        let browserModel = BrowserModel()
        Group {
            BrowserView(browserModel: browserModel)
                .environmentObject(GlobalModel.buildForPreview())
            BrowserView(browserModel: browserModel)
                .environmentObject(GlobalModel.buildForPreview())
                .preferredColorScheme(.dark)
        }
    }
}
#endif
