// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation
import SwiftUI

@MainActor
class Account: Identifiable, ObservableObject {
    let id: String
    @Published var name: String
    @Published var picture: UIImage
    @Published var wallets: [Address]
    @Published var dapps: [Dapp]

    required init(id: String, name: String, picture: UIImage, wallets: [Address], dapps: [Dapp]) {
        self.id = id
        self.name = name
        self.picture = picture
        self.wallets = wallets
        self.dapps = dapps
    }

    static func fromCore(_ core: AppCoreProtocol, _ account: CoreAccount) -> Self {
        let wallets = account.wallets.map { Address.fromCore(core, $0) }
        let dapps = account.dapps.map { Dapp.fromCore(core, $0) }
        let picture = UIImage(data: Data(account.picture)) ?? UIImage(systemName: "person")!
        return Self(id: account.id, name: account.name, picture: picture, wallets: wallets, dapps: dapps)
    }

    func isWallet(address: Address) -> Bool {
        wallets.contains(address)
    }

    func dappForAddress(address: Address) -> Dapp? {
        if let dapp = dapps.first(where: { $0.addresses.contains(address) }) {
            return dapp
        } else {
            return nil
        }
    }
}

// MARK: - Hashable

extension Account: Equatable, Hashable {

    static func == (lhs: Account, rhs: Account) -> Bool {
        return lhs.id == rhs.id
    }

    func hash(into hasher: inout Hasher) {
        hasher.combine(id)
    }

}

// MARK: - Display

extension Account {
    // SwiftUI image is not hashable
    var image: Image {
        Image(uiImage: picture)
    }

    var displayName: String {
        name
    }

    var topDapps: String {
        guard !dapps.isEmpty else {
            return "No dapps yet"
        }

        let maxDapps = 3

        var list = Array(dapps.prefix(maxDapps).map { $0.displayName })
        if dapps.count > maxDapps {
            list.append("...")
        }
        return ListFormatter.localizedString(byJoining: list)
    }
}

// MARK: - Search

extension Account {
    func matches(_ searchString: String) -> Bool {
        displayName.localizedCaseInsensitiveContains(searchString)
    }

    func getDappSearchSuggestions(searchString: String) -> [Dapp] {
        dapps.filter {
            $0.matches(searchString)
        }
    }
}

// MARK: - Development

#if DEBUG
    extension Account {
        convenience init(name: String, picture: UIImage, wallets: [Address], dapps: [Dapp]) {
            self.init(id: name.lowercased(), name: name, picture: picture, wallets: wallets, dapps: dapps)
        }
    }
#endif
