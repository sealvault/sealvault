// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct ChainMenu: View {
    @ObservedObject var address: Address

    var body: some View {
        Menu(address.chainDisplayName) {
            if let url = address.blockchainExplorerLink {
                Button(action: {
                    UIApplication.shared.open(url)
                }, label: {
                    Text("Open in Block Explorer")
                })
            }
        }
    }
}
