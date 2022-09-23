// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct TokenRow: View {
    var token: Token

    var body: some View {
        HStack {
            Label { Text(token.symbol).font(.headline) }
            icon: {
                    IconView(image: token.image, iconSize: 24)
                        .accessibility(label: Text(token.symbol))
                }

            Spacer()

            if token.amount.count > 12 {
                let prefix = String(token.amount.prefix(9))
                Text("\(prefix)...")
            } else {
                Text(token.amount)
            }
        }
    }
}

struct TokenRow_Previews: PreviewProvider {
    static var previews: some View {
        let token = Token.usdc()

        return TokenRow(token: token)
    }
}
