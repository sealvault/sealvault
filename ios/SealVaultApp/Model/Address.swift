// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation
import SwiftUI

class Address: Identifiable, ObservableObject {
    let core: AppCoreProtocol

    let id: String
    let checksumAddress: String
    let isWallet: Bool
    @Published var blockchainExplorerLink: URL?
    @Published var chain: CoreEthChain

    @Published var nativeToken: Token
    @Published var fungibleTokens: [String: Token]
    @Published var nfts: [String: NFT]
    @Published var loading: Bool = false

    var fungibleTokenList: [Token] {
        self.fungibleTokens.values.sorted(by: {$0.symbol < $1.symbol})
    }

    var nftList: [NFT] {
        self.nfts.values.sorted(by: {$0.displayName < $1.displayName})
    }

    required init(_ core: AppCoreProtocol, id: String, checksumAddress: String, isWallet: Bool,
                  blockchainExplorerLink: URL?, chain: CoreEthChain, nativeToken: Token) {
        self.core = core
        self.id = id
        self.checksumAddress = checksumAddress
        self.isWallet = isWallet
        self.blockchainExplorerLink = blockchainExplorerLink
        self.chain = chain
        self.nativeToken = nativeToken
        self.fungibleTokens = Dictionary()
        self.nfts = Dictionary()
    }

    static func fromCore(_ core: AppCoreProtocol, _ address: CoreAddress) -> Self {
        let url = URL(string: address.blockchainExplorerLink)
        let nativeToken = Token.fromCore(address.nativeToken)
        return Self(
            core, id: address.id, checksumAddress: address.checksumAddress, isWallet: address.isWallet,
            blockchainExplorerLink: url, chain: address.chain, nativeToken: nativeToken
        )
    }

    static func fetch(_ core: AppCoreProtocol, addressId: String) async -> Self? {
        let coreAddress: CoreAddress? = await dispatchBackground(.userInteractive) {
            do {
                return try core.fetchAddress(addressId: addressId)
            } catch {
                print("Failed to fetch address with error \(error)")
                return nil
            }
        }
        if let coreAddress = coreAddress {
            return Self.fromCore(core, coreAddress)
        } else {
            return nil
        }
    }

    static func convertIcon(_ icon: [UInt8]) -> UIImage {
        return UIImage(data: Data(icon)) ?? UIImage(systemName: "diamond")!
    }

    @MainActor
    func updateFromCore(_ address: CoreAddress) {
        withAnimation {
            assert(self.id == address.id, "id mismatch when updating address from core")
            assert(
                self.checksumAddress == address.checksumAddress,
                "checksum address mismatch when updating address from core"
            )
            // These values may become user configurable at some point
            self.blockchainExplorerLink = URL(string: address.blockchainExplorerLink)
            self.chain = address.chain
            self.updateNativeToken(address.nativeToken)
            self.nativeToken.updateFromCore(address.nativeToken)
        }
    }

    @MainActor
    func updateNativeToken(_ coreToken: CoreFungibleToken?) {
        if let token = coreToken {
            if token.id == self.nativeToken.id {
                self.nativeToken.updateFromCore(token)
            } else {
                self.nativeToken = Token.fromCore(token)
            }
        }
    }

    @MainActor
    func updateFungibleTokens(_ coreTokens: [CoreFungibleToken]) {
        let newIds = Set(coreTokens.map {$0.id})
        let oldIds = Set(self.fungibleTokens.keys)
        let toRemoveIds = oldIds.subtracting(newIds)
        for id in toRemoveIds {
            self.fungibleTokens.removeValue(forKey: id)
        }
        for coreToken in coreTokens {
            if let token = self.fungibleTokens[coreToken.id] {
                token.updateFromCore(coreToken)
            } else {
                self.fungibleTokens[coreToken.id] = Token.fromCore(coreToken)
            }
        }
    }

    @MainActor
    func updateNFTs(_ coreNFTs: [CoreNft]) {
        self.nfts = Dictionary()
        for coreNFT in coreNFTs {
            let nft = NFT.fromCore(coreNFT)
            self.nfts[nft.id] = nft
        }
    }

    @MainActor
    func updateTokens(_ tokens: CoreTokens) {
        self.updateNativeToken(tokens.nativeToken)
        self.updateFungibleTokens(tokens.fungibleTokens)
        self.updateNFTs(tokens.nfts)
    }

    private func fetchTokens() async -> CoreTokens? {
        return await dispatchBackground(.userInteractive) {
            do {
                return try self.core.tokensForAddressId(addressId: self.id)
            } catch {
                print("Failed to fetch tokens with error \(error)")
                return nil
            }
        }
    }

    @MainActor
    func refreshTokens() async {
        self.loading = true
        defer { self.loading = false }
        if let tokens = await self.fetchTokens() {
            self.updateTokens(tokens)
        }
    }
}

// MARK: - Hashable

extension Address: Equatable, Hashable {

    static func == (lhs: Address, rhs: Address) -> Bool {
        return lhs.id == rhs.id
    }

    func hash(into hasher: inout Hasher) {
        hasher.combine(id)
    }

}

// MARK: - display

extension Address {
    var addressDisplay: String {
        displayChecksumAddress(checksumAddress)
    }

    var image: Image {
        Image(uiImage: Self.convertIcon(chain.icon))
    }
}

// MARK: - chain

extension CoreEthChain: Identifiable {
    public var id: UInt64 {
        chainId
    }
}

// MARK: - preview

#if DEBUG
extension Address {
    static func ethereumWallet() -> Self {
        Self.ethereum(checksumAddress: "0xb3f5354C4c4Ca1E9314302CcFcaDc9de5da53AdA", isWallet: true)
    }

    static func ethereumDapp() -> Self {
        Self.ethereum(checksumAddress: "0xb3f5354C4c4Ca1E9314302CcFcaDc9de5da53AdA", isWallet: false)
    }

    static func polygonWallet() -> Self {
        Self.polygon(checksumAddress: "0xb3f5354C4c4Ca1E9314302CcFcaDc9de5da53AdA", isWallet: true)
    }

    static func polygonDapp() -> Self {
        Self.polygon(checksumAddress: "0x13Df6D6219C2CbbF01B4db01B58f28C5019B6D52", isWallet: false)
    }

    static func ethereum(checksumAddress: String, isWallet: Bool) -> Self {
        let nativeToken = Token.eth(checksumAddress)
        let icon = UIImage(named: "eth")!
        let explorer = URL(string: "https://etherscan.io/address/\(checksumAddress)")!
        let id = "ETH-\(checksumAddress)-\(isWallet)"
        let chain = Self.ethereumChain()
        return Self(
            PreviewAppCore(), id: id, checksumAddress: checksumAddress,
            isWallet: isWallet, blockchainExplorerLink: explorer, chain: chain, nativeToken: nativeToken
        )
    }

    static func polygon(checksumAddress: String, isWallet: Bool) -> Self {
        let nativeToken = Token.matic(checksumAddress)
        let icon = UIImage(named: "matic")!
        let explorer = URL(string: "https://polygonscan.com/address/\(checksumAddress)")!
        let id = "POLYGON-\(checksumAddress)-\(isWallet)"
        let chain = Self.polygonChain()
        return Self(
            PreviewAppCore(), id: id, checksumAddress: checksumAddress, isWallet: isWallet,
            blockchainExplorerLink: explorer, chain: chain, nativeToken: nativeToken
        )
    }

    static func ethereumChain() -> CoreEthChain {
        return CoreEthChain(chainId: 1, displayName: "Ethereum", isTestNet: false, canTrackToken: false,
                     icon: [UInt8](UIImage(named: "eth")!.pngData()!))
    }

    static func goerliChain() -> CoreEthChain {
        return CoreEthChain(chainId: 5, displayName: "Ethereum Goerli Testnet", isTestNet: true, canTrackToken: false,
                     icon: [UInt8](UIImage(named: "eth")!.pngData()!))
    }

    static func polygonChain() -> CoreEthChain {
        return CoreEthChain(chainId: 137, displayName: "Polygon PoS", isTestNet: false, canTrackToken: false,
                     icon: [UInt8](UIImage(named: "matic")!.pngData()!))
    }

    static func mumbaiChain() -> CoreEthChain {
        return CoreEthChain(chainId: 80001, displayName: "Polygon PoS Mumbai Testnet", isTestNet: true,
                     canTrackToken: false, icon: [UInt8](UIImage(named: "matic")!.pngData()!))
    }
}
#endif
