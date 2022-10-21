// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

// Hack to make the list of addresses update when a new address is added to a dapp
class Addresses: ObservableObject {
    @Published var dapp: Dapp?
    @Published var wallet: Address?

    var addresses: [Address] {
        if let dapp = self.dapp {
            return dapp.addressList
        } else if let wallet = self.wallet {
            return [wallet]
        } else {
            return []
        }
    }

    required init(dapp: Dapp?, wallet: Address?) {
        self.dapp = dapp
        self.wallet = wallet
    }
}

struct AddressView: View {
    var title: String
    let core: AppCoreProtocol
    @ObservedObject var account: Account
    @ObservedObject var addresses: Addresses
    @State var showAddChain: Bool = false

    var body: some View {
        ScrollViewReader { _ in
            // Need the `List` here for the `Section` in the `TokenView`
            List {
                ForEach(addresses.addresses) { address in
                    TokenView(account: account, address: address)
                }
                Section {} header: {
                    HStack {
                        Button {
                            showAddChain = true
                        } label: {
                            Text("Add Chain")
                        }
                    }
                }.headerProminence(.increased)
            }
            .refreshable(action: {
                for address in addresses.addresses {
                    // TODO parallelize, but take care of not exceeding rate limits
                    await address.refreshTokens()
                }
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
            if let address = addresses.addresses.first {
                AddChain(address: address)
                    .presentationDetents([.medium])
                    .background(.ultraThinMaterial)
            } else {
                Text("No address")
            }
        }
    }
}

#if DEBUG
struct AddressView_Previews: PreviewProvider {
    static var previews: some View {
        let model = GlobalModel.buildForPreview()
        let account = model.activeAccount!
        let dapp = Dapp.oneInch()
        // Simulate loading
        dapp.addressList[0].nativeToken.amount = nil
        let addresses = Addresses(dapp: dapp, wallet: nil)

        return AddressView(title: "Wallet", core: model.core, account: account, addresses: addresses)
    }
}
#endif
