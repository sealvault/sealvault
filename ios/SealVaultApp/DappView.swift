// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct DappView: View {
    var account: Account
    var dapp: Dapp

    @State private var searchString: String = ""
    @State private var selectedToken: Token?

    var body: some View {
        ScrollViewReader { _ in
            List {
                ForEach(dapp.addressesByChain.sorted(by: { $0.key < $1.key }), id: \.key) { _, value in
                    ForEach(value) { address in
                        TokenView(account: account, address: address)
                    }
                }
            }
        }
        .navigationTitle(Text(dapp.displayName))
        .navigationBarTitleDisplayMode(.inline)
        .toolbar {
            ToolbarItem(placement: .navigationBarTrailing) {
                AccountImageCircle(account: account)
            }
        }
    }
}

struct DappView_Previews: PreviewProvider {
    static var previews: some View {
        let model = ViewModel.buildForPreview()
        let account = model.activeAccount
        let dapp = account.dapps[0]
        return DappView(account: account, dapp: dapp)
    }
}
