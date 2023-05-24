// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct ChainLabel: View {
    @ObservedObject var address: Address

    var body: some View {
        Label {
            Text(address.chain.displayName)
        }
        icon: {
            IconView(image: address.image, iconSize: 24)
                .accessibility(label: Text(address.chain.displayName))
        }
    }
}
