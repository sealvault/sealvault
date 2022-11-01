// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation

@MainActor
class GlobalModel: ObservableObject {
    @Published var accounts: [String: Account]
    /// The account currently used for dapp interactions
    @Published var activeAccountId: String?
    @Published var callbackModel: CallbackModel
    @Published var browserOneUrl: URL?
    @Published var browserTwoUrl: URL?

    var activeAccount: Account? {
        return accountList.first(where: { acc in acc.id == activeAccountId })
    }

    var accountList: [Account] {
        accounts.values.sorted(by: {$0.displayName.lowercased() < $1.displayName.lowercased()})
    }

    let core: AppCoreProtocol

    required init(core: AppCoreProtocol, accounts: [Account], activeAccountId: String?, callbackModel: CallbackModel) {
        self.core = core
        self.accounts = Dictionary(uniqueKeysWithValues: accounts.map { ($0.id, $0) })
        self.activeAccountId = activeAccountId
        self.callbackModel = callbackModel
    }

    private func updateAccounts(_ coreAccounts: [CoreAccount]) {
        let newIds = Set(coreAccounts.map {$0.id})
        let oldIds = Set(self.accounts.keys)
        let toRemoveIds = oldIds.subtracting(newIds)
        for id in toRemoveIds {
            self.accounts.removeValue(forKey: id)
        }
        for coreAccount in coreAccounts {
            if let account = self.accounts[coreAccount.id] {
                account.updateFromCore(coreAccount)
            } else {
                let account = Account.fromCore(self.core, coreAccount)
                self.accounts[account.id] = account
            }
        }
    }

    static func buildOnStartup() -> Self {
        let coreArgs = CoreArgs(cacheDir: cacheDir(), dbFilePath: ensureDbFilePath())
        let callbackModel = CallbackModel()
        var core: AppCoreProtocol
        do {
            core = try AppCore(args: coreArgs, uiCallback: CoreUICallback(callbackModel))
        } catch {
            print("Failed to create core: \(error)")
            exit(1)
        }
        return Self(core: core, accounts: [], activeAccountId: nil, callbackModel: callbackModel)
    }

    private static func ensureDbFilePath() -> String {
        let dataProtectionAttributes = [
            FileAttributeKey.protectionKey: FileProtectionType.completeUntilFirstUserAuthentication
        ]

        let fileManager = FileManager.default
        let documentsURL = fileManager.urls(for: .documentDirectory, in: .userDomainMask).first!

        let dbDirPath = documentsURL.appendingPathComponent(Config.dbFileDir)
        if !fileManager.fileExists(atPath: dbDirPath.path) {
            // App can't start if it can't create this directory
            // swiftlint:disable force_try
            try! fileManager.createDirectory(
                atPath: dbDirPath.path, withIntermediateDirectories: true, attributes: dataProtectionAttributes
            )
            // swiftlint:enable force_try
        }

        let dbFilePath = dbDirPath.appendingPathComponent(Config.dbFileName)
        if !fileManager.fileExists(atPath: dbFilePath.path) {
            fileManager.createFile(atPath: dbFilePath.path, contents: nil, attributes: dataProtectionAttributes)
        }

        return dbFilePath.path
    }

    private static func cacheDir() -> String {
        let fileManager = FileManager.default
        let cacheDirUrl = fileManager.urls(for: .cachesDirectory, in: .userDomainMask).first!

        return cacheDirUrl.path
    }

    private func listAccounts(_ qos: DispatchQoS.QoSClass) async -> [CoreAccount]? {
        return await dispatchBackground(qos) {
            do {
                return try self.core.listAccounts()
            } catch {
                print("Error fetching account data: \(error)")
                return nil
            }
        }
    }

    private func fetchActiveAccountId(_ qos: DispatchQoS.QoSClass) async -> String? {
        return await dispatchBackground(qos) {
            do {
                return try self.core.activeAccountId()
            } catch {
                print("Error fetching active account id: \(error)")
                return nil
            }
        }
    }

    func refreshAccounts() async {
        let accounts = await self.listAccounts(.userInteractive)
        let activeAccountId = await self.fetchActiveAccountId(.userInteractive)

        if let accounts = accounts {
            self.updateAccounts(accounts)
        }
        if let activeAccountId = activeAccountId {
            self.activeAccountId = activeAccountId
        }
    }

    func addEthChain(chainId: UInt64, addressId: String) async {
        await dispatchBackground(.userInteractive) {
            do {
                try self.core.addEthChain(chainId: chainId, addressId: addressId)
            } catch {
                print("Error adding eth chain \(chainId): \(error)")
            }
        }
        // Make sure newly added chain shows up
        await self.refreshAccounts()
    }

    func changeDappChain(accountId: String, dappId: String, newChainId: UInt64) async {
        await dispatchBackground(.userInteractive) {
            do {
                let args = EthChangeDappChainArgs(accountId: accountId, dappId: dappId, newChainId: newChainId)
                try self.core.ethChangeDappChain(args: args)
            } catch {
                print("Error changing dapp address for dapp: \(error)")
            }
        }
        // Make sure newly added chain shows up
        await self.refreshAccounts()
    }

    func listEthChains() async -> [CoreEthChain] {
        return await dispatchBackground(.userInteractive) {
            self.core.listEthChains()
        }
    }

}

// MARK: - Development

#if DEBUG
// swiftlint:disable force_try
import SwiftUI
/// The App Core is quite heavy as it runs migrations etc on startup, and we don't need it for preview, so we just
/// pass this stub.
class PreviewAppCore: AppCoreProtocol {
    static func toCoreAccount(_ account: Account) -> CoreAccount {
        let picture = [UInt8](account.picture.pngData()!)
        let wallets = account.walletList.map(Self.toCoreAddress)
        let dapps = account.dappList.map(Self.toCoreDapp)
        return CoreAccount(
            id: account.id, name: account.name, picture: picture, wallets: wallets, dapps: dapps,
            createdAt: "2022-08-01", updatedAt: "2022-08-01"
        )
    }

    static func toCoreDapp(_ dapp: Dapp) -> CoreDapp {
        let icon = [UInt8](dapp.favicon.pngData()!)
        let url = dapp.url?.absoluteString ?? "https://ens.domains"
        let addresses = dapp.addressList.map(Self.toCoreAddress)

        return CoreDapp(
            id: dapp.id, accountId: dapp.accountId, humanIdentifier: dapp.humanIdentifier, url: url,
            addresses: addresses, selectedAddressId: dapp.selectedAddressId, favicon: icon, lastUsed: dapp.lastUsed
        )
    }

    static func toCoreAddress(_ address: Address) -> CoreAddress {
        let icon = [UInt8](address.chainIcon.pngData()!)
        let nativeToken = Self.toCoreToken(address.nativeToken)
        let blockchainExplorerLink = address.blockchainExplorerLink?.absoluteString ?? "https://etherscani.io"
        return CoreAddress(
            id: address.id, isWallet: address.isWallet, checksumAddress: address.checksumAddress,
            blockchainExplorerLink: blockchainExplorerLink, chainDisplayName: address.chainDisplayName,
            isTestNet: address.isTestNet, chainIcon: icon, nativeToken: nativeToken
        )
    }

    static func toCoreToken(_ token: Token) -> CoreToken {
        let icon = [UInt8](token.icon.pngData()!)
        return CoreToken(
            id: token.id, symbol: token.symbol, amount: token.amount, tokenType: TokenType.native, icon: icon
        )
    }

    func fungibleTokensForAddress(addressId: String) throws -> [CoreToken] {
        let tokens = DispatchQueue.main.sync {
            // Force update with new ids
            [Token.dai(UUID().uuidString), Token.usdc(UUID().uuidString), Token.busd(UUID().uuidString)]
        }
        Thread.sleep(forTimeInterval: 1)
        return DispatchQueue.main.sync {
            return tokens.map(Self.toCoreToken)
        }
    }

    func nativeTokenForAddress(addressId: String) throws -> CoreToken {
        let token = DispatchQueue.main.sync {
            return Token.matic(UUID().uuidString)
        }
        Thread.sleep(forTimeInterval: 1)
        return DispatchQueue.main.sync {
            return Self.toCoreToken(token)
        }
    }

    func fetchFavicon(rawUrl: String) throws -> [UInt8]? {
        nil
    }

    func dappIdentifier(rawUrl: String) throws -> String {
        let url = URL(string: rawUrl)!
        return url.host!
    }

    func ethTransferFungibleToken(
        args: EthTransferFungibleTokenArgs
    ) throws {
        throw CoreError.Fatal(message: "not implemented")
    }

    func ethTransferNativeToken(args: EthTransferNativeTokenArgs) throws {
        throw CoreError.Fatal(message: "not implemented")
    }

    func ethTransactionBlockExplorerUrl(fromAddressId _: String, txHash _: String) throws -> String {
        throw CoreError.Fatal(message: "not implemented")
    }

    func listAccounts() throws -> [CoreAccount] {
        let wallets = [
            Address.ethereumWallet(),
            Address.polygonWallet()
        ]
        let activeAccountName = "alice.eth"
        let activeAccountId = try! self.activeAccountId()

        let accounts = [
            Account(
                self,
                id: activeAccountId, name: activeAccountName, picture: UIImage(named: "cat-green")!,
                wallets: wallets,
                dapps: [
                    Dapp.ens(),
                    Dapp.opensea(),
                    Dapp.uniswap(),
                    Dapp.dhedge(),
                    Dapp.sushi(),
                    Dapp.aave(),
                    Dapp.oneInch(),
                    Dapp.quickswap(),
                    Dapp.darkForest(),
                    Dapp.dnd()
                ]
            ),
            Account(
                self,
                id: "2", name: "DeFi Anon", picture: UIImage(named: "orangutan")!, wallets: wallets,
                dapps: [Dapp.dhedge(), Dapp.sushi(), Dapp.aave(), Dapp.oneInch(), Dapp.quickswap(), Dapp.uniswap()]
            ),
            Account(
                self,
                id: "3", name: "Dark Forest General", picture: UIImage(named: "owl-chatty")!, wallets: wallets,
                dapps: [Dapp.darkForest()]
            ),
            Account(
                self,
                id: "4", name: "D&D Magician", picture: UIImage(named: "dog-derp")!, wallets: wallets,
                dapps: [Dapp.dnd()]
            ),
            Account(
                self,
                id: "5", name: "NSFW", picture: UIImage(named: "dog-pink")!, wallets: wallets,
                dapps: [Dapp.opensea()]
            )
        ]

        return accounts.map(Self.toCoreAccount)
    }

    func activeAccountId() throws -> String {
        return "1"
    }

    func getInPageScript(rpcProviderName _: String, requestHandlerName _: String) throws -> String {
        throw CoreError.Fatal(message: "not implemented")
    }

    func inPageRequest(context _: InPageRequestContextI, rawRequest _: String) throws {
        throw CoreError.Fatal(message: "not implemented")
    }

    func userApprovedDapp(context: InPageRequestContextI, params: DappApprovalParams) throws {
        throw CoreError.Fatal(message: "not implemented")
    }

    func userRejectedDapp(context: InPageRequestContextI, params: DappApprovalParams) throws {
        throw CoreError.Fatal(message: "not implemented")
    }

    func addEthChain(chainId: UInt64, addressId: String) throws {
        throw CoreError.Fatal(message: "not implemented")
    }

    func ethChangeDappChain(args: EthChangeDappChainArgs) throws {
        throw CoreError.Fatal(message: "not implemented")
    }

    func listEthChains() -> [CoreEthChain] {
        [
            CoreEthChain(chainId: 1, displayName: "Ethereum"),
            CoreEthChain(chainId: 5, displayName: "Ethereum Goerli Testnet"),
            CoreEthChain(chainId: 137, displayName: "Polygon PoS"),
            CoreEthChain(chainId: 80001, displayName: "Polygon PoS Mumbai Testnet")
        ]
    }
}

extension GlobalModel {
    static func buildForPreview() -> GlobalModel {
        let core = PreviewAppCore()
        let accounts = try! core.listAccounts().map { Account.fromCore(core, $0) }
        let activeAccountId = try! core.activeAccountId()
        return GlobalModel(
            core: core, accounts: accounts, activeAccountId: activeAccountId, callbackModel: CallbackModel()
        )
    }
}
// swiftlint:enable force_try
#endif
