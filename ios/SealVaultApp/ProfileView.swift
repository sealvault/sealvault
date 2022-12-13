// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

@MainActor
struct ProfileView: View {
    @EnvironmentObject private var model: GlobalModel
    @ObservedObject var profile: Profile

    var body: some View {
        ScrollViewReader { _ in
            List {
                NavigationLink {
                    AddressView(
                        title: "Wallet", core: model.core, profile: profile,
                        addresses: Addresses(profile: profile)
                    )
                } label: {
                    WalletRow(profile: profile)
                        .accessibilityIdentifier("\(profile.displayName) profile wallet")
                }
                Section {
                    ForEach(profile.dappList) { dapp in
                        NavigationLink {
                            AddressView(
                                title: dapp.humanIdentifier, core: model.core, profile: profile,
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
                                .accessibilityIdentifier("\(dapp.displayName) dapp")
                        }
                    }
                } header: {
                    Text("Dapps")
                }
            }
            .refreshable(action: {
                await model.refreshProfiles()
            })
            .accessibilityRotor("Dapps", entries: profile.dappList, entryLabel: \.displayName)
        }
        .navigationTitle(Text(profile.displayName))
        .navigationBarTitleDisplayMode(.inline)
        .task {
            await self.model.refreshProfiles()
        }
    }
}

#if DEBUG
struct ProfileView_Previews: PreviewProvider {
    static var previews: some View {
        let model = GlobalModel.buildForPreview()
        return ProfileView(profile: model.activeProfile!).environmentObject(model)
    }
}
#endif
