// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

// Hack to only call refresh tokens once per address
struct NativeTokenRow: View {
    @ObservedObject var address: Address

    var body: some View {
        TokenRow(token: address.nativeToken)
    }
}

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

            // Progress bar is next to chain name
            TokenAmount(token: token, showProgress: false)
        }
    }
}

struct NFTRow: View {
    @ObservedObject var nft: NFT

    var body: some View {
        HStack {
            Label {
                Text(nft.displayName).font(.headline)
            } icon: {
                Image(systemName: "photo.artframe")
            }

            Spacer()
        }
    }
}
