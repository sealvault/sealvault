// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation
import SwiftUI

@MainActor
class Token: Identifiable, ObservableObject {
    let id: String
    let symbol: String
    let icon: UIImage
    @Published var amount: String?
    let nativeToken: Bool

    required init(id: String, symbol: String, icon: UIImage, amount: String?, nativeToken: Bool) {
        self.id = id
        self.symbol = symbol
        self.icon = icon
        self.amount = amount
        self.nativeToken = nativeToken
    }

    static func fromCore(_ token: CoreToken) -> Self {
        var tokenIcon: UIImage?
        if let icon = token.icon {
            tokenIcon = UIImage(data: Data(icon))
        }
        let tokenIconOrFallback = tokenIcon ?? UIImage(systemName: "banknote")!
        return self.init(
            id: token.id,
            symbol: token.symbol,
            icon: tokenIconOrFallback,
            amount: token.amount,
            nativeToken: token.tokenType == TokenType.native
        )
    }
}

// MARK: - Hashable

extension Token: Equatable, Hashable {

    static func == (lhs: Token, rhs: Token) -> Bool {
        return lhs.id == rhs.id
    }

    func hash(into hasher: inout Hasher) {
        hasher.combine(id)
    }
}

// MARK: - display

extension Token {
    var image: Image {
        Image(uiImage: icon)
    }
}

// MARK: - preview

#if DEBUG
    extension Token {
        static func eth() -> Token {
            let symbol = "ETH"
            let icon = UIImage(named: symbol.lowercased())!
            return Token(id: symbol, symbol: symbol, icon: icon, amount: "45.45122312", nativeToken: true)
        }

        static func matic() -> Token {
            let symbol = "MATIC"
            let icon = UIImage(named: symbol.lowercased())!
            return Token(id: symbol, symbol: symbol, icon: icon, amount: "0.9123", nativeToken: true)
        }

        static func usdc() -> Token {
            let symbol = "USDC"
            let icon = UIImage(named: symbol.lowercased())!
            return Token(id: symbol, symbol: symbol, icon: icon, amount: "123.45", nativeToken: false)
        }

        static func dai() -> Token {
            let symbol = "DAI"
            let icon = UIImage(named: symbol.lowercased())!
            return Token(id: symbol, symbol: symbol, icon: icon, amount: "4.321", nativeToken: false)
        }
    }
#endif
