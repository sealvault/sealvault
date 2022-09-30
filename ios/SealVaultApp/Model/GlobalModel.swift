// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation

@MainActor
class GlobalModel: ObservableObject {
    @Published var accounts: [Account]

    /// The account currently used for dapp interactions
    @Published var activeAccountId: String?
    var activeAccount: Account {
        return accounts.first(where: { acc in acc.id == activeAccountId })!
    }

    let core: AppCoreProtocol

    required init(core: AppCoreProtocol, accounts: [Account], activeAccountId: String?) {
        self.core = core
        self.accounts = accounts
        self.activeAccountId = activeAccountId
    }

    static func buildOnStartup() -> Self {
        let coreArgs = CoreArgs(cacheDir: cacheDir(), dbFilePath: ensureDbFilePath())
        var core: AppCore
        do {
            core = try AppCore(args: coreArgs)
        } catch {
            print("Failed to create core: \(error)")
            exit(1)
        }
        return Self(core: core, accounts: [], activeAccountId: nil)
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

    private func listAccounts(_ qos: DispatchQoS.QoSClass) async -> [Account] {
        return await dispatchBackground(qos) {
            var accounts: [Account] = []
            do {
                accounts = try self.core.listAccounts().map { Account.fromCore(self.core, $0) }
            } catch {
                print("Error fetching account data: \(error)")
            }
            return accounts
        }
    }

    private func fetchActiveAccountId(_ qos: DispatchQoS.QoSClass) async -> String? {
        return await dispatchBackground(qos) {
            var activeAccountId: String?
            do {
                activeAccountId = try self.core.activeAccountId()
            } catch {
                print("Error fetching active account id: \(error)")
            }
            return activeAccountId
        }
    }

    func refreshAccounts() async {
        self.accounts = await self.listAccounts(.userInteractive)
        self.activeAccountId = await self.fetchActiveAccountId(.userInteractive)
    }
}

// MARK: - Account & Address

extension GlobalModel {
    func getAccountSearchSugestions(searchString: String) -> [Account] {
        accounts.filter {
            $0.matches(searchString)
        }
    }
}

// MARK: - Development

#if DEBUG
import SwiftUI
/// The App Core is quite heavy as it runs migrations etc on startup, and we don't need it for preview, so we just
/// pass this stub.
class PreviewAppCore: AppCoreProtocol {
    static func toCoreToken(token: Token) -> CoreToken {
        return DispatchQueue.main.sync {
            let icon = [UInt8](token.icon.pngData()!)
            return CoreToken(
                id: token.id, symbol: token.symbol, amount: token.amount, tokenType: TokenType.native, icon: icon
            )
        }
    }

    func fungibleTokensForAddress(addressId: String) throws -> [CoreToken] {
        let tokens = DispatchQueue.main.sync {
            [Token.dai(), Token.usdc()]
        }
        Thread.sleep(forTimeInterval: 1)
        return tokens.map(Self.toCoreToken)
    }

    func nativeTokenForAddress(addressId: String) throws -> CoreToken {
        let token = DispatchQueue.main.sync {
            return Token.matic()
        }
        Thread.sleep(forTimeInterval: 1)
        return Self.toCoreToken(token: token)
    }

    func fetchFavicon(rawUrl: String) throws -> [UInt8]? {
        nil
    }

    func dappIdentifier(rawUrl: String) throws -> String {
        let url = URL(string: rawUrl)!
        return url.host!
    }

    func ethTransferFungibleToken(
        fromAddressId: String, toChecksumAddress: String, amount: String, tokenId: String
    ) throws -> String {
        throw CoreError.Fatal(message: "not implemented")
    }

    func ethTransferNativeToken(fromAddressId _: String, toChecksumAddress _: String, amount _: String) throws
    -> String {
        throw CoreError.Fatal(message: "not implemented")
    }

    func ethTransactionBlockExplorerUrl(fromAddressId _: String, txHash _: String) throws -> String {
        throw CoreError.Fatal(message: "not implemented")
    }

    func listAccounts() throws -> [CoreAccount] {
        throw CoreError.Fatal(message: "not implemented")
    }

    func activeAccountId() throws -> String {
        throw CoreError.Fatal(message: "not implemented")
    }

    func getInPageScript(rpcProviderName _: String, requestHandlerName _: String) throws -> String {
        throw CoreError.Fatal(message: "not implemented")
    }

    func inPageRequest(context _: InPageRequestContextI, rawRequest _: String) throws -> String {
        throw CoreError.Fatal(message: "not implemented")
    }
}

extension GlobalModel {
    static func buildForPreview() -> GlobalModel {
        let dapps = [
            Dapp.opensea(),
            Dapp.sushi(),
            Dapp.uniswap()
        ]
        let wallets = [
            Address.ethereumWallet(),
            Address.polygonWallet()
        ]
        let activeAccountName = "alice.eth"
        let accounts = [
            Account(
                id: "1", name: activeAccountName, picture: UIImage(named: "cat-green")!, wallets: wallets,
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
                id: "2", name: "DeFi Anon", picture: UIImage(named: "orangutan")!, wallets: wallets,
                dapps: [Dapp.dhedge(), Dapp.sushi(), Dapp.aave(), Dapp.oneInch(), Dapp.quickswap(), Dapp.uniswap()]
            ),
            Account(
                id: "3", name: "Dark Forest General", picture: UIImage(named: "owl-chatty")!, wallets: wallets,
                dapps: [Dapp.darkForest()]
            ),
            Account(
                id: "4", name: "D&D Magician", picture: UIImage(named: "dog-derp")!, wallets: wallets,
                dapps: [Dapp.dnd()]
            ),
            Account(
                id: "5", name: "NSFW", picture: UIImage(named: "dog-pink")!, wallets: wallets,
                dapps: [Dapp.opensea()]
            )
        ]

        let core = PreviewAppCore()

        return GlobalModel(core: core, accounts: accounts, activeAccountId: "1")
    }
}
#endif
