// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

protocol DappApprovalRequestI: Identifiable {
    var accountId: String { get }

    var dappHumanIdentifier: String { get }

    var favicon: [UInt8]? { get }

    func approve()

    func reject()

}

struct DappApprovalRequest: DappApprovalRequestI {
    // It's important to have a unique id per request
    let id = UUID()
    let context: InPageRequestContext
    let params: DappApprovalParams

    var accountId: String {
        params.accountId
    }

    var dappHumanIdentifier: String {
        params.dappIdentifier
    }

    var favicon: [UInt8]? {
        params.favicon
    }

    func approve() {
        do {
            try self.context.core.userApprovedDapp(context: self.context, params: self.params)
        } catch {
            print("userApprovedDapp threw: \(error)")
        }
    }

    func reject() {
        do {
            try self.context.core.userRejectedDapp(context: context, params: self.params)
        } catch {
            print("userApprovedDapp threw: \(error)")
        }
    }

}

struct DappApproval: View {
    @EnvironmentObject private var viewModel: GlobalModel
    @Environment(\.dismiss) var dismiss

    @State var request: any DappApprovalRequestI

    private var account: Account {
        viewModel.accountList.first(where: { $0.id == request.accountId })!
    }

    private var dappIcon: Image {
        let image = Dapp.faviconWithFallback(request.favicon)
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
                    request.reject()
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
    }
}

#if DEBUG

struct DappApprovalRequestPreview: DappApprovalRequestI {
    var id = UUID()
    var accountId: String
    var dappHumanIdentifier: String
    var favicon: [UInt8]?

    func approve() {
        print("dapp approval request approved")
    }

    func reject() {
        print("dapp approval request rejected")
    }

    @MainActor
    static func buildForPreview(_ accountId: String) -> Self {
        let dapp = Dapp.uniswap()
        let favicon = [UInt8](dapp.favicon.pngData()!)
        let request = DappApprovalRequestPreview(
            accountId: accountId,
            dappHumanIdentifier: dapp.humanIdentifier,
            favicon: favicon
        )
        return request
    }

}

struct DappApproval_Previews: PreviewProvider {
    static var previews: some View {
        let model = GlobalModel.buildForPreview()
        let request = DappApprovalRequestPreview.buildForPreview(model.activeAccountId!)
        DappApproval(request: request).environmentObject(model)
    }
}
#endif
