// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct TokenView: View {
    var account: Account
    var address: Address

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
            ForEach(address.fungibleTokens) { token in
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
        } header: { Text("Fungible Tokens") }
    }
}

struct TokenView_Previews: PreviewProvider {
    static var previews: some View {
        let model = ViewModel.buildForPreview()
        let account = model.activeAccount
        let dapp = account.dapps[0]
        let address: Address = dapp.addressesByChain.values.first!.first!

        return TokenView(account: account, address: address)
    }
}
