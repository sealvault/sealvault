// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation
import SwiftUI

struct Address: Identifiable, Hashable {
    var id: String
    var checksumAddress: String
    var blockchainExplorerLink: URL?
    var chainDisplayName: String
    var chainIcon: UIImage

    var nativeToken: Token
    var fungibleTokens: [Token]

    static func fromCore(_ address: CoreAddress) -> Self {
        let chainIcon = UIImage(data: Data(address.chainIcon)) ?? UIImage(systemName: "diamond")!
        let url = URL(string: address.blockchainExplorerLink)
        let nativeToken = Token.fromCore(address.nativeToken)
        var fungibleTokens = address.fungibleTokens.map(Token.fromCore)
        fungibleTokens.sort {$0.symbol < $1.symbol}
        return Self(
            id: address.id, checksumAddress: address.checksumAddress, blockchainExplorerLink: url,
            chainDisplayName: address.chainDisplayName, chainIcon: chainIcon, nativeToken: nativeToken,
            fungibleTokens: fungibleTokens
        )
    }
}

// MARK: - display

extension Address {
    var addressDisplay: String {
        "\(checksumAddress.prefix(5))...\(checksumAddress.suffix(3))"
    }

    var image: Image {
        Image(uiImage: chainIcon)
    }
}

// MARK: - preview

#if DEBUG
    extension Address {
        static func ethereumWallet() -> Self {
            Self.ethereum(checksumAddress: "0xb3f5354C4c4Ca1E9314302CcFcaDc9de5da53AdA")
        }

        static func polygonWallet() -> Self {
            Self.polygon(checksumAddress: "0xb3f5354C4c4Ca1E9314302CcFcaDc9de5da53AdA")
        }

        static func ethereumDapp() -> Self {
            Self.ethereum(checksumAddress: "0x696e931B0d3112FebAA9401A89C2658f96C725f2")
        }

        static func polygonDapp() -> Self {
            Self.polygon(checksumAddress: "0x696e931B0d3112FebAA9401A89C2658f96C725f2")
        }

        static func ethereum(checksumAddress: String) -> Self {
            let fungibleTokens = [Token.dai(), Token.usdc()]
            let icon = UIImage(named: "eth")!
            let explorer = URL(string: "https://etherscan.io/address/\(checksumAddress)")!
            let id = "eth-\(checksumAddress)"
            return Self(
                id: id, checksumAddress: "0xb3f5354C4c4Ca1E9314302CcFcaDc9de5da53AdA",
                blockchainExplorerLink: explorer, chainDisplayName: "Ethereum", chainIcon: icon,
                nativeToken: Token.eth(), fungibleTokens: fungibleTokens
            )
        }

        static func polygon(checksumAddress: String) -> Self {
            let fungibleTokens = [Token.dai(), Token.usdc()]
            let icon = UIImage(named: "matic")!
            let explorer = URL(string: "https://polygonscan.com/address/\(checksumAddress)")!
            let id = "polygon-pos-\(checksumAddress)"
            return Self(
                id: id, checksumAddress: checksumAddress, blockchainExplorerLink: explorer,
                chainDisplayName: "Polygon PoS", chainIcon: icon, nativeToken: Token.matic(),
                fungibleTokens: fungibleTokens
            )
        }
    }
#endif
