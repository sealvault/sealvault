// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct TokenView: View {
    @ObservedObject var profile: Profile
    @ObservedObject var address: Address
    @State var showImportToken: Bool = false
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
                ChainMenu(address: address, showImportToken: $showImportToken)
                if address.loading {
                    ProgressView()
                } else if profile.isAddressSelectedForAdapp(addressId: address.id) {
                    Image(systemName: "checkmark.circle")
                        .foregroundColor(.green)
                }
            }
            .padding(.top, paddingTop)
            .scaledToFit()
        }
        .headerProminence(.increased)
        .sheet(isPresented: $showImportToken) {
            ImportToken(userAddress: address)
                    .presentationDetents([.medium])
                    .background(.ultraThinMaterial)
        }

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
