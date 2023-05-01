// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation
import SwiftUI

class Dapp: Identifiable, ObservableObject {
    let core: AppCoreProtocol
    /// Database identifier
    let id: String
    /// The profile that the dapp belongs to
    let profileId: String
    /// Human readable identifier that is either the origin or the registrable domain
    @Published var humanIdentifier: String
    @Published var url: URL?
    @Published var addresses: MultichainAddress
    @Published var selectedAddressId: String?
    @Published var lastUsed: String?

    /// Favicon
    @Published var favicon: UIImage?

    required init(
        _ core: AppCoreProtocol, id: String, profileId: String, humanIdentifier: String, url: URL?,
        addresses: [Address], selectedAddressId: String?, lastUsed: String?, favicon: UIImage
    ) {
        self.core = core
        self.id = id
        self.profileId = profileId
        self.humanIdentifier = humanIdentifier
        self.url = url
        self.addresses = MultichainAddress(core, addresses)
        self.selectedAddressId = selectedAddressId
        self.lastUsed = lastUsed
        self.favicon = favicon
    }

    static func fromCore(_ core: AppCoreProtocol, _ dapp: CoreDapp) -> Self {
        let url = URL(string: dapp.url)
        let addresses = dapp.addresses.map { Address.fromCore(core, $0) }
        return self.init(
            core,
            id: dapp.id,
            profileId: dapp.profileId,
            humanIdentifier: dapp.humanIdentifier,
            url: url,
            addresses: addresses,
            selectedAddressId: dapp.selectedAddressId,
            lastUsed: dapp.lastUsed,
            favicon: Self.faviconWithFallback(dapp.favicon)
        )
    }

    static func faviconWithFallback(_ rawIcon: [UInt8]?) -> UIImage {
        var favicon: UIImage?
        if let icon = rawIcon {
            favicon = UIImage(data: Data(icon))
        }
        let faviconOrFallback = favicon ?? UIImage(systemName: "app")!
        return faviconOrFallback
    }

    @MainActor
    func updateFromCore(_ dapp: CoreDapp) {
        assert(self.id == dapp.id, "id mismatch in dapp update from core")
        self.humanIdentifier = dapp.humanIdentifier
        self.url = URL(string: dapp.url)
        self.selectedAddressId = dapp.selectedAddressId
        self.addresses.updateAddresses(dapp.addresses)
        self.lastUsed = dapp.lastUsed
        self.favicon = Self.faviconWithFallback(dapp.favicon)
    }
}

// MARK: - Hashable

extension Dapp: Equatable, Hashable {

    static func == (lhs: Dapp, rhs: Dapp) -> Bool {
        return lhs.id == rhs.id
    }

    func hash(into hasher: inout Hasher) {
        hasher.combine(id)
    }

}

// MARK: - display

extension Dapp {
    var displayName: String {
        humanIdentifier
    }

    var image: Image? {
        favicon.map {Image(uiImage: $0)}
    }
}

// MARK: - Search

extension Dapp {
    func matches(_ searchString: String) -> Bool {
        return displayName.localizedCaseInsensitiveContains(searchString)
    }
}

// MARK: - preview

#if DEBUG
// swiftlint:disable force_try
    extension Dapp {
        static func build(
            id: String, humanIdentifier: String, url: URL?, addresses: [Address], favicon: UIImage
        ) -> Self {
            let core = PreviewAppCore()
            let activeProfileId = try! core.activeProfileId()
            return Self(
                core,
                id: id, profileId: activeProfileId, humanIdentifier: id, url: url, addresses: addresses,
                selectedAddressId: addresses.first!.id, lastUsed: "2022-08-01", favicon: favicon
            )

        }

        static func uniswap() -> Self {
            let id = "uniswap.org"
            let url = URL(string: "https://\(id)")
            let favicon = UIImage(named: "uniswap")!
            let addresses = [Address.polygonDapp()]
            return build(
                id: id, humanIdentifier: id, url: url, addresses: addresses, favicon: favicon
            )
        }

        static func sushi() -> Self {
            let id = "sushi.com"
            let url = URL(string: "https://\(id)")
            let favicon = UIImage(named: "sushi")!
            let addresses = [Address.polygonDapp()]
            return build(
                id: id, humanIdentifier: id, url: url, addresses: addresses, favicon: favicon
            )
        }

        static func opensea() -> Self {
            let id = "opensea.io"
            let url = URL(string: "https://\(id)")
            let favicon = UIImage(named: "opensea")!
            let addresses = [Address.polygonDapp()]
            return build(
                id: id, humanIdentifier: id, url: url, addresses: addresses, favicon: favicon
            )
        }

        static func ens() -> Self {
            let id = "ens.domains"
            let url = URL(string: "https://\(id)")
            let favicon = UIImage(named: "ens")!
            let addresses = [Address.polygonDapp()]
            return build(
                id: id, humanIdentifier: id, url: url, addresses: addresses, favicon: favicon
            )
        }

        static func aave() -> Self {
            let id = "aave.com"
            let url = URL(string: "https://\(id)")
            let favicon = UIImage(named: "aave")!
            let addresses = [Address.polygonDapp()]
            return build(
                id: id, humanIdentifier: id, url: url, addresses: addresses, favicon: favicon
            )
        }

        static func dnd() -> Self {
            let id = "raritymmo.com"
            let url = URL(string: "https://\(id)")
            let favicon = UIImage(named: "dnd")!
            let addresses = [Address.polygonDapp()]
            return build(
                id: id, humanIdentifier: id, url: url, addresses: addresses, favicon: favicon
            )
        }

        static func darkForest() -> Self {
            let id = "zkga.me"
            let url = URL(string: "https://\(id)")
            let favicon = UIImage(named: "darkforest")!
            let addresses = [Address.polygonDapp()]
            return build(
                id: id, humanIdentifier: id, url: url, addresses: addresses, favicon: favicon
            )
        }

        static func dhedge() -> Self {
            let id = "dhedge.org"
            let url = URL(string: "https://\(id)")
            let favicon = UIImage(named: "dhedge")!
            let addresses = [Address.polygonDapp()]
            return build(
                id: id, humanIdentifier: id, url: url, addresses: addresses, favicon: favicon
            )
        }

        static func oneInch() -> Self {
            let id = "1inch.io"
            let url = URL(string: "https://\(id)")
            let favicon = UIImage(named: "1inch")!
            let addresses = [Address.polygonDapp()]
            return build(
                id: id, humanIdentifier: id, url: url, addresses: addresses, favicon: favicon
            )
        }

        static func quickswap() -> Self {
            let id = "quickswap.exchange"
            let url = URL(string: "https://\(id)")
            let favicon = UIImage(named: "quickswap")!
            let addresses = [Address.polygonDapp()]
            return build(
                id: id, humanIdentifier: id, url: url, addresses: addresses, favicon: favicon
            )
        }

        static func lilNouns() -> Self {
            let id = "lilnouns.wtf"
            let url = URL(string: "https://\(id)")
            let favicon = UIImage(named: "nouns")!
            let addresses = [Address.ethereumDapp()]
            return build(
                id: id, humanIdentifier: id, url: url, addresses: addresses, favicon: favicon
            )
        }

        static func poap() -> Self {
            let id = "poap.xyz"
            let url = URL(string: "https://\(id)")
            let favicon = UIImage(named: "poap")!
            let addresses = [Address.ethereumDapp()]
            return build(
                id: id, humanIdentifier: id, url: url, addresses: addresses, favicon: favicon
            )
        }

        static func xmpt() -> Self {
            let id = "xmtp.chat"
            let url = URL(string: "https://\(id)")
            let favicon = UIImage(named: "xmtp")!
            let addresses = [Address.polygonDapp()]
            return build(
                id: id, humanIdentifier: id, url: url, addresses: addresses, favicon: favicon
            )
        }

    }
// swiftlint:enable force_try
#endif
