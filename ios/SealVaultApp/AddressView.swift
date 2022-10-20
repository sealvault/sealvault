// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct AddressView: View {
    let title: String
    let core: AppCoreProtocol
    @ObservedObject var account: Account
    @ObservedObject var address: Address
    @State var showAddChain: Bool = false

    var body: some View {
        ScrollViewReader { _ in
            // Need the `List` here for the `Section` in the `TokenView`
            List {
                TokenView(account: account, address: address, showAddChain: $showAddChain)
            }
            .refreshable(action: {
                await address.refreshTokens()
            })
        }
        .navigationTitle(Text(title))
        .navigationBarTitleDisplayMode(.inline)
        .toolbar {
            ToolbarItem(placement: .navigationBarTrailing) {
                AccountImageCircle(account: account)
            }
        }
        .sheet(isPresented: $showAddChain) {
            AddChain(address: address)
                .presentationDetents([.medium])
                .background(.ultraThinMaterial)
        }
        .task {
            await self.address.refreshTokens()
        }
    }
}

#if DEBUG
struct AddressView_Previews: PreviewProvider {
    static var previews: some View {
        let model = GlobalModel.buildForPreview()
        let account = model.activeAccount!
        let address = account.wallets.values.first!
        address.nativeToken.amount = nil

        return AddressView(title: "Wallet", core: model.core, account: account, address: address)
    }
}
#endif
