// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

@MainActor
struct DappApprovalRequest: Identifiable {
    // It's important to have a unique id per request
    var id = UUID()
    let accountId: String
    let dappHumanIdentifier: String
    let dappFavicon: [UInt8]?
    let approve: () -> Void
    let dismiss: () -> Void
}

#if DEBUG
extension DappApprovalRequest {
    static func buildForPreview(_ accountId: String) -> Self {
        let dapp = Dapp.uniswap()
        let favicon = [UInt8](dapp.favicon.pngData()!)
        let request = DappApprovalRequest(
            accountId: accountId,
            dappHumanIdentifier: dapp.humanIdentifier,
            dappFavicon: favicon,
            approve: {},
            dismiss: {}
        )
        return request
    }
}
#endif

struct DappApproval: View {
    @EnvironmentObject private var viewModel: GlobalModel
    @Environment(\.dismiss) var dismiss
    @Environment(\.isPresented) private var isPresented

    @State var request: DappApprovalRequest

    private var account: Account {
        viewModel.accountList.first(where: { $0.id == request.accountId })!
    }

    private var dappIcon: Image {
        let image = Dapp.faviconWithFallback(request.dappFavicon)
        return Image(uiImage: image)
    }

    var body: some View {
        VStack(spacing: 20) {
            Spacer()

            VStack(spacing: 20) {
                HStack {
                    Text("Add").fontWeight(.light)
                    Label {
                        Text(request.dappHumanIdentifier)
                    } icon: {
                        IconView(image: dappIcon, iconSize: 40)
                                .accessibility(label: Text("Dapp icon"))
                    }
                }
                .font(.largeTitle)
                HStack {
                    Text("to").fontWeight(.light)
                    Label {
                        Text(account.displayName)
                    } icon: {
                        AccountImageCircle(account: account).accessibilityLabel("account image")
                    }
                    Text("account").fontWeight(.light)
                }
                .font(.title2)
            }

            Spacer()

            HStack(spacing: 0) {
                Button(action: {
                    dismiss()
                }, label: {
                    Text("Cancel").frame(maxWidth: .infinity).foregroundColor(.secondary)
                })
                .accessibilityLabel("rejectDapp")
                .buttonStyle(.borderless)
                .controlSize(.large)

                Button(action: {
                    request.approve()
                    dismiss()
                }, label: {
                    Text("OK").frame(maxWidth: .infinity)
                })
                .accessibilityLabel("approveDapp")
                .buttonStyle(.borderless)
                .controlSize(.large)
            }
        }
        .onDisappear {
            // Make sure signal is called no matter how the view disappears (eg by swiping instead of tapping a button).
            request.dismiss()
        }
    }
}

struct DappApproval_Previews: PreviewProvider {
    static var previews: some View {
        let model = GlobalModel.buildForPreview()
        let request = DappApprovalRequest.buildForPreview(model.activeAccountId!)
        DappApproval(request: request).environmentObject(model)
    }
}
