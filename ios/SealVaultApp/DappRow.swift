// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct DappRow: View {
    @ObservedObject var dapp: Dapp

    var body: some View {
        Label {
            Text(dapp.displayName)
                .font(.headline)
        } icon: {
            IconView(image: dapp.image, iconSize: 24)
                .accessibility(label: Text("Dapp icon"))
        }
    }
}

struct DappRow_Previews: PreviewProvider {
    static var previews: some View {
        let dapp = Dapp.uniswap()
        return DappRow(dapp: dapp)
    }
}
