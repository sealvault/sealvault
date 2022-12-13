// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

// Hack to make the list of addresses update when a new address is added to an Profile or dapp
class Addresses: ObservableObject {
    @Published var dapp: Dapp?
    @Published var account: Account?
    @Published var selectedAddressId: String?

    var firstAddress: Address? {
        self.addresses.first
    }

    var addresses: [Address] {
        if let dapp = self.dapp {
            return dapp.addressList
        } else if let account = self.account {
            return account.walletList
        } else {
            return []
        }
    }

    var isDapp: Bool {
        self.dapp != nil
    }

    init(dapp: Dapp) {
        self.dapp = dapp
        self.account = nil
    }

    init(account: Account) {
        self.dapp = nil
        self.account = account
    }

}

struct AddressView: View {
    var title: String
    let core: AppCoreProtocol
    @ObservedObject var account: Account
    @ObservedObject var addresses: Addresses
    @State var showChainSelection: Bool = false
    @State var showSwitchAddress: Bool = false
    @EnvironmentObject private var model: GlobalModel

    var paddingTop: CGFloat = 50

    var chainSelectionTitle: String {
        addresses.isDapp ? "Change Connected Chain" : "Add Chain"
    }

    var body: some View {
        ScrollViewReader { _ in
                List {
                    ForEach(Array(addresses.addresses.enumerated()), id: \.offset) { index, address in
                        TokenView(account: account, address: address, paddingTop: index == 0 ? 30 : paddingTop)
                    }
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
            if let address = addresses.firstAddress {
                AddressMenu(address: address) {
                    Button {
                        showChainSelection = true
                    } label: {
                        Text(chainSelectionTitle)
                    }
                }
            }
        }
        .sheet(isPresented: $showChainSelection) {
            ChainSelection(title: chainSelectionTitle) { newChainId in
                if let dapp = addresses.dapp {
                    await model.changeDappChain(accountId: dapp.accountId, dappId: dapp.id, newChainId: newChainId)
                } else if let address = addresses.addresses.first {
                    await model.addEthChain(chainId: newChainId, addressId: address.id)
                } else {
                    print("error: no addresses")
                }
            }
            .presentationDetents([.medium])
            .background(.ultraThinMaterial)

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
        dapp.addressList[0].selectedForDapp = true
        let addresses = Addresses(dapp: dapp)

        return AddressView(title: "Wallet", core: model.core, account: account, addresses: addresses)
    }
}
#endif
