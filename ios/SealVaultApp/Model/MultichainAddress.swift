// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation

class MultichainAddress: Identifiable, ObservableObject {
    let core: AppCoreProtocol

    @Published var addresses: [String: Address]

    var addressList: [Address] {
        self.addresses.values.sorted(by: sortAddressesBy(_:_:))
    }

    var firstAddress: Address? {
        if let address = addressList.first {
            return address
        } else {
            return nil
        }
    }

    var checksumAddress: String? {
        firstAddress?.checksumAddress
    }

    var addressesByChain: [String: [Address]] {
        var result: [String: [Address]] = Dictionary()
        for address in addresses.values {
            result[address.chainDisplayName, default: []].append(address)
        }
        return result
    }

    required init(_ core: AppCoreProtocol, _ addresses: [Address]) {
        let checksumAddresses = Set(addresses.map { $0.checksumAddress })
        assert(checksumAddresses.count <= 1, "Expected all addresses to have the same checksum address")

        self.core = core
        self.addresses = Dictionary(uniqueKeysWithValues: addresses.map { ($0.id, $0) })
    }

    @MainActor
    func updateAddresses(_ coreAddresses: [CoreAddress]) {
        let newIds = Set(coreAddresses.map {$0.id})
        let oldIds = Set(self.addresses.keys)
        let toRemoveIds = oldIds.subtracting(newIds)
        for id in toRemoveIds {
            self.addresses.removeValue(forKey: id)
        }
        for coreAddr in coreAddresses {
            if let address = self.addresses[coreAddr.id] {
                address.updateFromCore(coreAddr)
            } else {
                let address = Address.fromCore(self.core, coreAddr)
                self.addresses[address.id] = address
            }
        }
    }

    @MainActor
    func updateTokens(_ coreTokens: [CoreTokens]) async {
        for tokens in coreTokens {
            if let address = self.addresses[tokens.addressId] {
                address.updateTokens(tokens)
            } else {
                print("new address \(tokens.addressId)")
                if let address = await Address.fetch(self.core, addressId: tokens.addressId) {
                    print("added new address \(address.id)")
                    address.updateTokens(tokens)
                    self.addresses[address.id] = address
                }
            }
        }
    }

    private func fetchTokens() async -> [CoreTokens] {
        if let checksumAddress = checksumAddress {
            return await dispatchBackground(.userInteractive) {
                do {
                    return try self.core.tokensForEthAddress(checksumAddress: checksumAddress)
                } catch {
                    print("Failed to fetch tokens with error \(error)")
                    return []
                }
            }
        } else {
            return []
        }
    }

    @MainActor
    func refreshTokens() async {
        for address in addressList {
            address.loading = true
        }
        defer {
            for address in addressList {
                address.loading = false
            }
        }

        let tokens = await fetchTokens()
        await updateTokens(tokens)
    }

}
