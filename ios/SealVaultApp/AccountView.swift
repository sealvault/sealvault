// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

@MainActor
struct AccountView: View {
    @EnvironmentObject private var model: GlobalModel
    @ObservedObject var account: Account

    var body: some View {
        ScrollViewReader { _ in
            List {
                NavigationLink {
                    AddressView(
                        title: "Wallet", core: model.core, account: account,
                        addresses: Addresses(account: account)
                    )
                } label: {
                    WalletRow(account: account)
                }
                Section {
                    ForEach(account.dappList) { dapp in
                        NavigationLink {
                            AddressView(
                                title: dapp.humanIdentifier, core: model.core, account: account,
                                addresses: Addresses(dapp: dapp)
                            )
                        } label: {
                            DappRow(dapp: dapp).accessibilityIdentifier(dapp.displayName)
                                .contextMenu {
                                    Button(action: {
                                        if let url = dapp.url {
                                            model.browserOneUrl = url
                                        }
                                    }, label: {
                                        Text("Open in Browser 1")
                                    })
                                    Button(action: {
                                        if let url = dapp.url {
                                            model.browserTwoUrl = url
                                        }
                                    }, label: {
                                        Text("Open in Browser 2")
                                    })
                                }
                        }
                    }
                } header: {
                    Text("Dapps")
                }
            }
            .refreshable(action: {
                await model.refreshAccounts()
            })
            .accessibilityRotor("Dapps", entries: account.dappList, entryLabel: \.displayName)
        }
        .navigationTitle(Text(account.displayName))
        .navigationBarTitleDisplayMode(.inline)
        .task {
            await self.model.refreshAccounts()
        }
    }
}

#if DEBUG
struct AccountView_Previews: PreviewProvider {
    static var previews: some View {
        let model = GlobalModel.buildForPreview()
        return AccountView(account: model.activeAccount!).environmentObject(model)
    }
}
#endif
