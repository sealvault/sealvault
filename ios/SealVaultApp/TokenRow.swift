// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct TokenRow: View {
    @ObservedObject var token: Token

    var body: some View {
        HStack {
            Label {
                Text(token.symbol).font(.headline)

            } icon: {
                IconView(image: token.image, iconSize: 24)
                    .accessibility(label: Text(token.symbol))
            }

            Spacer()

            TokenAmount(token: token)
        }
    }
}

// Hack to only call refresh tokens once per address
struct NativeTokenRow: View {
    @ObservedObject var address: Address

    var body: some View {
        TokenRow(token: address.nativeToken)
            .task {
                await address.refreshTokens()
            }
    }
}
