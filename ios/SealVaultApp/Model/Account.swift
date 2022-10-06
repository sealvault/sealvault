// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation
import SwiftUI

@MainActor
class Account: Identifiable, ObservableObject {
    let core: AppCoreProtocol
    let id: String
    @Published var name: String
    @Published var picture: UIImage
    @Published var wallets: [String: Address]
    @Published var dapps: [String: Dapp]

    var walletList: [Address] {
        self.wallets.values.sorted(by: { $0.chainDisplayName < $1.chainDisplayName })
    }

    var dappList: [Dapp] {
        self.dapps.values.sorted(by: { $0.displayName < $1.displayName })
    }

    var allAddresses: [Address] {
        let dappAddressList: [Address] = self.dappList.flatMap {$0.addressList}
        return self.walletList + dappAddressList
    }

    required init(
        _ core: AppCoreProtocol, id: String, name: String, picture: UIImage, wallets: [Address], dapps: [Dapp]
    ) {
        self.core = core
        self.id = id
        self.name = name
        self.picture = picture
        self.wallets = Dictionary(uniqueKeysWithValues: wallets.map { ($0.id, $0) })
        self.dapps = Dictionary(uniqueKeysWithValues: dapps.map { ($0.id, $0) })
    }

    static func fromCore(_ core: AppCoreProtocol, _ account: CoreAccount) -> Self {
        let wallets = account.wallets.map { Address.fromCore(core, $0) }
        let dapps = account.dapps.map { Dapp.fromCore(core, $0) }
        let picture = Self.convertPicture(account.picture)
        return Self(core, id: account.id, name: account.name, picture: picture, wallets: wallets, dapps: dapps)
    }

    static func convertPicture(_ picture: [UInt8]) -> UIImage {
        return UIImage(data: Data(picture)) ?? UIImage(systemName: "person")!
    }

    func updateFromCore(_ account: CoreAccount) {
        assert(account.id == self.id, "account id mismatch on update")
        self.name = account.name
        self.picture = Self.convertPicture(account.picture)
        self.updateWallets(account.wallets)
        self.updateDapps(account.dapps)
    }

    private func updateWallets(_ coreAddresses: [CoreAddress]) {
        let newIds = Set(coreAddresses.map {$0.id})
        let oldIds = Set(self.wallets.keys)
        let toRemoveIds = oldIds.subtracting(newIds)
        for id in toRemoveIds {
            self.wallets.removeValue(forKey: id)
        }
        for coreAddr in coreAddresses {
            if let address = self.wallets[coreAddr.id] {
                address.updateFromCore(coreAddr)
            } else {
                let address = Address.fromCore(self.core, coreAddr)
                self.wallets[address.id] = address
            }
        }
    }

    private func updateDapps(_ coreDapps: [CoreDapp]) {
        let newIds = Set(coreDapps.map {$0.id})
        let oldIds = Set(self.dapps.keys)
        let toRemoveIds = oldIds.subtracting(newIds)
        for id in toRemoveIds {
            self.dapps.removeValue(forKey: id)
        }
        for coreDapp in coreDapps {
            if let dapp = self.dapps[coreDapp.id] {
                dapp.updateFromCore(coreDapp)
            } else {
                let dapp = Dapp.fromCore(self.core, coreDapp)
                self.dapps[dapp.id] = dapp
            }
        }
    }

    func dappForAddress(address: Address) -> Dapp? {
        if let dapp = dappList.first(where: { $0.addresses[address.id] != nil }) {
            return dapp
        } else {
            return nil
        }
    }

    func addressForAddressId(addressId: String) -> Address? {
        self.allAddresses.first(where: {$0.id == addressId})
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

        var list = Array(dappList.prefix(maxDapps).map { $0.displayName })
        if dapps.count > maxDapps {
            list.append("...")
        }
        return ListFormatter.localizedString(byJoining: list)
    }
}

// MARK: - Development

#if DEBUG
    extension Account {
        convenience init(name: String, picture: UIImage, wallets: [Address], dapps: [Dapp]) {
            let core = PreviewAppCore()
            self.init(core, id: name.lowercased(), name: name, picture: picture, wallets: wallets, dapps: dapps)
        }
    }
#endif
