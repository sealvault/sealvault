// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct TokenView: View {
    @ObservedObject var profile: Profile
    @ObservedObject var address: Address
    @State var showImportToken: Bool = false
    @State var showTransferNativeToken = false
    @State var showTransferToken = false

    var paddingTop: CGFloat

    var body: some View {
        Section {
            Button {
                showTransferNativeToken = true
            } label: {
                NativeTokenRow(address: address)
            }
            .accessibilityLabel(address.nativeToken.symbol)
            .sheet(isPresented: $showTransferNativeToken) {
                TransferForm(state: TransferState(profile: profile, token: address.nativeToken, fromAddress: address))
                    .presentationDetents([.large])
                    .background(.ultraThinMaterial)
            }

            ForEach(address.fungibleTokenList) { token in
                TokenTransferButton(profile: profile, token: token, address: address)
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

struct TokenTransferButton: View {
    @ObservedObject var profile: Profile
    @ObservedObject var token: Token
    @ObservedObject var address: Address

    @State var showTransferToken: Bool = false

    var body: some View {
        Button {
            showTransferToken = true
        } label: {
            TokenRow(token: token)
        }
        .accessibilityLabel(token.symbol)
        .sheet(isPresented: $showTransferToken) {
            TransferForm(state: TransferState(profile: profile, token: token, fromAddress: address))
                .presentationDetents([.large])
                .background(.ultraThinMaterial)
        }
    }
}
