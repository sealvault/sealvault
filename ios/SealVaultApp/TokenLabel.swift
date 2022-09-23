// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct TokenLabel: View {
    var token: Token

    var body: some View {
        Label {
            Text(token.symbol)
        }
        icon: {
            IconView(image: token.image, iconSize: 24)
                .accessibility(label: Text(token.symbol))
        }
    }
}
