// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct WalletRow: View {
    var address: Address

    var body: some View {
        Label {
            Text(address.chainDisplayName)
                .font(.headline)
        } icon: {
            IconView(image: address.image, iconSize: 24)
                .accessibility(label: Text("Chain icon"))
        }
    }
}

struct WalletRow_Previews: PreviewProvider {
    static var previews: some View {
        let address = Address.ethereumWallet()
        return WalletRow(address: address)
    }
}
