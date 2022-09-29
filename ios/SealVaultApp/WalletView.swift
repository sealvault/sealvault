// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct WalletView: View {
    var account: Account
    @StateObject var address: Address

    var body: some View {
        AddressView(title: "Wallet", account: account, address: address)
    }
}

struct WalletView_Previews: PreviewProvider {
    static var previews: some View {
        let model = GlobalModel.buildForPreview()
        let account = model.activeAccount
        let dapp = account.dapps[0]
        let address: Address = dapp.addressesByChain.values.first!.first!

        return WalletView(account: account, address: address)
    }
}
