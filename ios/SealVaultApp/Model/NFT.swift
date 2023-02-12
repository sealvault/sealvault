// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation

class NFT: Identifiable, ObservableObject {
    let id: String
    let displayName: String

    required init(id: String, displayName: String) {
        self.id = id
        self.displayName = displayName
    }

    static func fromCore(_ nft: CoreNft) -> Self {

        return self.init(
            id: nft.id,
            displayName: nft.displayName
        )
    }
}

// MARK: - preview

#if DEBUG
    extension NFT {
        static func example() -> NFT {
            let name = "NFT #123"
            return NFT(id: name, displayName: name)
        }
    }
#endif
