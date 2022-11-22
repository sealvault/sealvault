// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct AccountListView: View {
    @EnvironmentObject private var model: GlobalModel

    var body: some View {
        VStack {
            ScrollViewReader { _ in
                List {
                    ForEach(model.accountList) { account in
                        NavigationLink {
                            AccountView(account: account)
                        } label: {
                            AccountRow(account: account)
                                .padding(.vertical, 8)
                                .accessibilityIdentifier("\(account.displayName) account")
                        }
                    }
                }
                .accessibilityRotor("Accounts", entries: model.accountList, entryLabel: \.displayName)
                .refreshable(action: {
                    await model.refreshAccounts()
                })
            }
            .navigationTitle(Text("Accounts"))
            .task {
                await self.model.refreshAccounts()
            }

//            Divider()
        }
    }
}

#if DEBUG
struct AccountListView_Previews: PreviewProvider {
    static var previews: some View {
        Group {
            AccountListView().environmentObject(GlobalModel.buildForPreview())
        }
    }
}
#endif
