// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

class DappApprovalRequest: Identifiable, ObservableObject {
    // It's important to have a unique id per request
    let id = UUID()
    // Optional for preview
    let context: InPageRequestContext?
    var params: DappApprovalParams

    init(context: InPageRequestContext?, params: DappApprovalParams) {
        self.context = context
        self.params = params
    }

    func approve() {
        guard let context = self.context else {
            return
        }
        do {
            try context.core.userApprovedDapp(context: context, params: self.params)
        } catch {
            print("userApprovedDapp threw: \(error)")
        }
    }

    func reject() {
        guard let context = self.context else {
            print("No context, returning")
            return
        }
        do {
            try context.core.userRejectedDapp(context: context, params: self.params)
        } catch {
            print("userApprovedDapp threw: \(error)")
        }
    }

}

struct DappApproval: View {
    @EnvironmentObject private var viewModel: GlobalModel
    @Environment(\.dismiss) var dismiss

    @ObservedObject var request: DappApprovalRequest

    private var profile: Profile {
        viewModel.profileList.first(where: { $0.id == request.params.profileId })!
    }

    private var dappIcon: Image {
        let image = Dapp.faviconWithFallback(request.params.favicon)
        return Image(uiImage: image)
    }

    var body: some View {
        VStack(spacing: 20) {
            HStack {
                Text("Create new key for dapp")
                    .font(.title)
            }
            .padding(.horizontal, 20)
            .padding(.top, 40)

            Spacer()

            VStack(spacing: 20) {
                HStack {
                    Label {
                        Text(request.params.dappIdentifier)
                    } icon: {
                        IconView(image: dappIcon, iconSize: 40)
                                .accessibility(label: Text("Dapp icon"))
                    }
                }
                .font(.largeTitle)
                HStack {
                    Label {
                        Text(profile.displayName)
                    } icon: {
                        ProfileImageCircle(profile: profile)
                            .accessibilityLabel("Profile Picture")
                    }
                    Text("profile").fontWeight(.light)
                }
                .font(.title2)

            }
            .scaledToFit()

            Spacer()

            DialogButtons(onApprove: {
                request.approve()
                dismiss()
            }, onReject: {
                request.reject()
                dismiss()
            })
        }
    }
}

#if DEBUG

struct DappApproval_Previews: PreviewProvider {
    static var previews: some View {
        let model = GlobalModel.buildForPreview()
        let profileId = model.activeProfileId!
        let dapp = Dapp.quickswap()
        let favicon = [UInt8](dapp.favicon!.pngData()!)
        let params = DappApprovalParams(
            profileId: profileId, dappIdentifier: dapp.humanIdentifier, favicon: favicon, amount: "0.1",
            transferAllotment: false, tokenSymbol: "MATIC", chainDisplayName: "Polygon PoS", chainId: 137,
            jsonRpcRequest: ""
        )
        let request = DappApprovalRequest(context: nil, params: params)
        DappApproval(request: request).environmentObject(model)
    }
}
#endif
