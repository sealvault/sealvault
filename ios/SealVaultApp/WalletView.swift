// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct WalletView: View {
    var account: Account
    @StateObject var address: Address

    @State private var searchString: String = ""
    @State private var selectedToken: Token?

    var body: some View {
        ScrollViewReader { _ in
            // Need the `List` here for the `Section` in the `TokenView`
            List {
                TokenView(account: account, address: address)
            }
        }
        .navigationTitle(Text("Wallet"))
        .navigationBarTitleDisplayMode(.inline)
        .toolbar {
            ToolbarItem(placement: .navigationBarTrailing) {
                AccountImageCircle(account: account)
            }
        }
        .task {
            await self.address.refreshNativeToken()
        }
    }
}

struct AddressView_Previews: PreviewProvider {
    static var previews: some View {
        let model = GlobalModel.buildForPreview()
        let account = model.activeAccount
        let dapp = account.dapps[0]
        let address: Address = dapp.addressesByChain.values.first!.first!

        return WalletView(account: account, address: address)
    }
}
