// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct TokenView: View {
    @ObservedObject var profile: Profile
    @ObservedObject var address: Address
    var paddingTop: CGFloat

    var body: some View {
        Section {
            NavigationLink {
                TransferForm(state: TransferState(profile: profile, token: address.nativeToken, fromAddress: address))
                    .navigationBarTitleDisplayMode(.inline)
            } label: {
                NativeTokenRow(address: address)
            }
            .accessibilityLabel(address.nativeToken.symbol)
            ForEach(address.fungibleTokenList) { token in
                NavigationLink {
                    TransferForm(state: TransferState(profile: profile, token: token, fromAddress: address))
                        .navigationBarTitleDisplayMode(.inline)
                } label: {
                    TokenRow(token: token)
                }.accessibilityLabel(token.symbol)
            }
        } header: {
            HStack(spacing: 5) {
                Text(address.chainDisplayName)
                if profile.isAddressSelectedForAdapp(addressId: address.id) {
                    Image(systemName: "checkmark.circle")
                        .foregroundColor(.green)
                }
            }
            .padding(.top, paddingTop)
            .scaledToFit()
        }
        .headerProminence(.increased)

        if !address.nftList.isEmpty {
            Section {
                ForEach(address.nftList) { nft in
                    NFTRow(nft: nft)
                }
            } header: {
                Text("NFTs")
            }
            .headerProminence(.standard)
        }
    }
}
