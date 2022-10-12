// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct AppTabNavigation: View {
    enum Tab {
        case accountList
        case webBrowser
    }

    @EnvironmentObject private var model: GlobalModel
    @State var selection: Tab = .accountList

    var body: some View {
        TabView(selection: $selection) {
            NavigationView {
                AccountListView()
            }
            .tabItem {
                let menuText = Text("Accounts", comment: "Accounts tab title")

                Label {
                    menuText
                } icon: {
                    // TODO: size isn't respected
                    // IconView(image: model.activeAccount.image, iconSize: 16)
                    Image(systemName: "key")
                }.accessibility(label: menuText)
            }
            .tag(Tab.accountList)

            NavigationView {
                BrowserView()
            }
            .tabItem {
                let menuText = Text("Browser", comment: "Web browser menu tab title")
                Label {
                    menuText
                } icon: {
                    Image(systemName: "network")
                }.accessibility(label: menuText)
            }
            .tag(Tab.webBrowser)
        }.navigationViewStyle(StackNavigationViewStyle())
    }
}

#if DEBUG
struct AppTabNavigation_Previews: PreviewProvider {
    static var previews: some View {
        AppTabNavigation(selection: .webBrowser).environmentObject(GlobalModel.buildForPreview())
        AppTabNavigation(selection: .accountList).environmentObject(GlobalModel.buildForPreview())
    }
}
#endif
