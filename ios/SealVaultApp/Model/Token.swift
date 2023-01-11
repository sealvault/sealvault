// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation
import SwiftUI

class Token: Identifiable, ObservableObject {
    let id: String
    let symbol: String
    @Published var icon: UIImage
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

        return self.init(
            id: token.id,
            symbol: token.symbol,
            icon: Self.convertIcon(token.icon),
            amount: token.amount,
            nativeToken: token.tokenType == TokenType.native
        )
    }

    static func convertIcon(_ maybeIcon: [UInt8]?) -> UIImage {
        var tokenIcon: UIImage?
        if let icon = maybeIcon {
            tokenIcon = UIImage(data: Data(icon))
        }
        return tokenIcon ?? UIImage(systemName: "banknote")!
    }

    func updateFromCore(_ token: CoreToken) {
        assert(self.id == token.id, "token id mismatch in update from core")
        assert(self.symbol == token.symbol, "symbol mismatch in update from core")
        self.icon = Self.convertIcon(token.icon)
        // Tokens are listed without amounts first when fetching profiles.
        // Don't unset amount if we have fetched the amount for this token already.
        if token.amount != nil {
            self.amount = token.amount
        }
        switch token.tokenType {
        case .native:
            assert(self.nativeToken, "native token mismatch in update from core")
        case .fungible:
            assert(!self.nativeToken, "fungible token mismatch in update from core")
        }

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
        static func eth(_ address: String) -> Token {
            let symbol = "ETH"
            let id = "\(symbol)-\(address)"
            let icon = UIImage(named: symbol.lowercased())!
            return Token(id: id, symbol: symbol, icon: icon, amount: "45.51", nativeToken: true)
        }

        static func matic(_ address: String) -> Token {
            let symbol = "MATIC"
            let id = "\(symbol)-\(address)"
            let icon = UIImage(named: symbol.lowercased())!
            return Token(id: id, symbol: symbol, icon: icon, amount: "236.91", nativeToken: true)
        }

        static func usdc(_ address: String) -> Token {
            let symbol = "USDC"
            let id = "\(symbol)-\(address)"
            let icon = UIImage(named: symbol.lowercased())!
            return Token(id: id, symbol: symbol, icon: icon, amount: "133.45", nativeToken: false)
        }

        static func dai(_ address: String) -> Token {
            let symbol = "DAI"
            let id = "\(symbol)-\(address)"
            let icon = UIImage(named: symbol.lowercased())!
            return Token(id: id, symbol: symbol, icon: icon, amount: "4.32", nativeToken: false)
        }

        static func busd(_ address: String) -> Token {
            let symbol = "BUSD"
            let id = "\(symbol)-\(address)"
            let icon = UIImage(named: symbol.lowercased())!
            return Token(id: id, symbol: symbol, icon: icon, amount: "15.64", nativeToken: false)
        }
    }
#endif
