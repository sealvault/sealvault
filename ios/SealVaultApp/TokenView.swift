// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct TokenView: View {
    @ObservedObject var account: Account
    @ObservedObject var address: Address

    var body: some View {
        Section {
            NavigationLink {
                TransferForm(account: account, fromAddress: address, token: address.nativeToken)
                    .navigationBarTitleDisplayMode(.inline)
                    .toolbar {
                        ToolbarItem(placement: .navigationBarTrailing) {
                            AccountImageCircle(account: account)
                        }
                    }
            } label: {
                TokenRow(token: address.nativeToken)
            }
        } header: {
            HStack {
                Text(address.chainDisplayName)
                Spacer()
                AddressMenu(address: address).textCase(.none)
            }
        }
        .headerProminence(.standard)
        Section {
            ForEach(address.fungibleTokenList) { token in
                NavigationLink {
                    TransferForm(account: account, fromAddress: address, token: token)
                        .navigationBarTitleDisplayMode(.inline)
                        .toolbar {
                            ToolbarItem(placement: .navigationBarTrailing) {
                                AccountImageCircle(account: account)
                            }
                        }
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
                Text("No Tokens")
            }
        }
    }
}
