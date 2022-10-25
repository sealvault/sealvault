// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct TokenView: View {
    @ObservedObject var account: Account
    @ObservedObject var address: Address
    var paddingTop: CGFloat

    var body: some View {
        Section {
            NavigationLink {
                TransferForm(state: TransferState(account: account, token: address.nativeToken, fromAddress: address))
                    .navigationBarTitleDisplayMode(.inline)
            } label: {
                NativeTokenRow(address: address)
            }
        } header: {
            HStack {
                Text(address.chainDisplayName)
            }
            .padding(.top, paddingTop)
            .scaledToFit()
        }
        .headerProminence(.increased)
        Section {
            ForEach(address.fungibleTokenList) { token in
                NavigationLink {
                    TransferForm(state: TransferState(account: account, token: token, fromAddress: address))
                        .navigationBarTitleDisplayMode(.inline)
                } label: {
                    TokenRow(token: token)
                }
            }
        } header: {
            if address.loading {
                ProgressView()
            } else if !address.fungibleTokens.isEmpty {
                Text("Fungible Tokens")
            } else {
                Text("No other tokens")
            }
        }
    }
}
