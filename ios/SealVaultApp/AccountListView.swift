// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct AccountListView: View {
    @EnvironmentObject private var model: ViewModel
    @State private var selectedAccount: Account?
    @State private var searchString: String = ""

    var listedAccounts: [Account] {
        let filteredAccounts = searchString.isEmpty ? model.accounts : model.accounts.filter {
            $0.matches(searchString)
        }
        return filteredAccounts.sorted(by: { $0.displayName.localizedCompare($1.displayName) == .orderedAscending })
    }

    var body: some View {
        ScrollViewReader { _ in
            List {
                ForEach(listedAccounts) { account in
                    NavigationLink(tag: account, selection: $selectedAccount) {
                        AccountView(account: account)
                    } label: {
                        AccountRow(account: account).padding(.vertical, 8).accessibilityIdentifier(account.displayName)
                    }
                    .swipeActions {
                        Button {
                            withAnimation {
                                selectedAccount = account
                            }
                        } label: {
                            Label {
                                Text("Set Active")
                            } icon: {
                                Image(systemName: "pin")
                            }
                        }
                        .tint(.accentColor)
                    }
                }
            }
            .accessibilityRotor("Accounts", entries: model.accounts, entryLabel: \.displayName)
            .searchable(text: $searchString) {
                let searchResults = model.getAccountSearchSugestions(searchString: searchString)
                ForEach(searchResults) { suggestion in
                    Text(suggestion.displayName).searchCompletion(suggestion.displayName)
                }
            }
            .refreshable(action: { await model.refreshAccounts() })
        }
        .navigationTitle(Text("Accounts"))
    }
}

struct AccountListView_Previews: PreviewProvider {
    static var previews: some View {
        Group {
            AccountListView().environmentObject(ViewModel.buildForPreview())
        }
    }
}
