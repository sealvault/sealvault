// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct AddressView: View {
    var title: String
    let core: AppCoreProtocol
    @ObservedObject var profile: Profile
    let dapp: Dapp?
    @ObservedObject var addresses: MultichainAddress

    @State var showChainSelection: Bool = false
    @State var showSwitchAddress: Bool = false
    @EnvironmentObject private var model: GlobalModel

    var paddingTop: CGFloat = 50

    var chainSelectionTitle: String {
        dapp != nil ? "Change Connected Network" : "Add Network"
    }

    var body: some View {
        ScrollViewReader { _ in
            List {
                ForEach(Array(addresses.addressList.enumerated()), id: \.offset) { index, address in
                    TokenView(profile: profile, address: address, paddingTop: index == 0 ? 30 : paddingTop)
                }
            }
            .refreshable(action: {
                await addresses.refreshTokens()
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
                if let dapp = dapp {
                    await model.changeDappChain(profileId: dapp.profileId, dappId: dapp.id, newChainId: newChainId)
                } else if let address = addresses.firstAddress {
                    await model.addEthChain(chainId: newChainId, addressId: address.id)
                } else {
                    print("error: no addresses")
                }
                await addresses.refreshTokens()
            }
            .presentationDetents([.medium])
            .background(.ultraThinMaterial)
        }
        .task {
            await addresses.refreshTokens()
        }
    }
}

#if DEBUG
struct AddressView_Previews: PreviewProvider {
    static var previews: some View {
        let model = GlobalModel.buildForPreview()
        let profile = model.activeProfile!
        let dapp = Dapp.oneInch()
        // Simulate loading
        if let address = dapp.addresses.firstAddress {
            address.nativeToken.amount = nil
            dapp.selectedAddressId = address.id
        }

        return AddressView(title: "Wallet", core: model.core, profile: profile, dapp: dapp, addresses: dapp.addresses)
    }
}
#endif
