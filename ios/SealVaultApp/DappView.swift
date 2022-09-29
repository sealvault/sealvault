// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct DappView: View {
    var account: Account
    @ObservedObject var dapp: Dapp

    var body: some View {
        AddressView(title: dapp.displayName, account: account, address: dapp.addresses.first!)
    }
}

struct DappView_Previews: PreviewProvider {
    static var previews: some View {
        let model = GlobalModel.buildForPreview()
        let account = model.activeAccount
        let dapp = account.dapps[0]
        return DappView(account: account, dapp: dapp)
    }
}
