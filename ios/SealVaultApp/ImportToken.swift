// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct ImportToken: View {
    @EnvironmentObject private var model: GlobalModel
    @EnvironmentObject private var bannerModel: BannerModel

    @Environment(\.dismiss) var dismiss

    @State var userAddress: Address
    @State var tokenAddress: String = ""

    @State var approveDisabled: Bool = true
    @State var loading: Bool = false

    @ScaledMetric var vStackSpacing: CGFloat = 20

    private let cornerRadius: Double = 10

    var body: some View {
        VStack(spacing: vStackSpacing) {
            SheetTitle(title: "Import Token")

            Spacer()

            Form {
                TextField("Enter ERC20 token address", text: $tokenAddress)
                    .accessibilityLabel("Enter ERC20 token address")
                    .disableAutocorrection(true)
            }
            .scrollDisabled(true)

            DialogButtons(onApprove: {
                Task {
                    DispatchQueue.main.async {
                        loading = true
                    }
                    defer {
                        DispatchQueue.main.async {
                            loading = false
                        }
                    }
                    let maybeErrorBanner = await model.importToken(userAddress: userAddress, tokenAddress: tokenAddress
                    )
                    DispatchQueue.main.async {
                        if let bannerData = maybeErrorBanner {
                            self.bannerModel.bannerData = bannerData
                        }
                        dismiss()
                    }
                    await userAddress.refreshTokens()
                }
            }, onReject: {
                dismiss()
            }, approveDisabled: $approveDisabled, loading: $loading)
        }
        .background(Color(UIColor.systemGray6))
        .onChange(of: tokenAddress) { newValue in
            if approveDisabled && !newValue.isEmpty {
                approveDisabled = false
            } else if newValue.isEmpty {
                approveDisabled = true
            }
        }
    }
}

#if DEBUG
struct ImportToken_Previews: PreviewProvider {
    static var previews: some View {
        let address = Address.polygonWallet()
        ImportToken(userAddress: address)
            .environmentObject(GlobalModel.buildForPreview())
            .preferredColorScheme(.dark)
    }
}
#endif
