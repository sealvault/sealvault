// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation

@MainActor
class ViewModel: ObservableObject {
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
            exit(1)
        }
        var accounts: [Account] = []
        do {
            accounts = try core.listAccounts().map(Account.fromCore)
        } catch {
            print("Error fetching account data: \(error)")
        }
        var activeAccountId: String?
        do {
            activeAccountId = try core.activeAccountId()
        } catch {
            print("Error fetching active account id: \(error)")
        }
        return Self(core: core, accounts: accounts, activeAccountId: activeAccountId)
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

    private func listAccounts() async -> [Account] {
        // TODO: make a generic dispatch + continuation wrapper
        func dispatch(completion: @escaping ([Account]) -> Void) {
            DispatchQueue.global(qos: .background).async {
                var accounts: [Account] = []
                do {
                    accounts = try self.core.listAccounts().map(Account.fromCore)
                } catch {
                    print("Error fetching account data: \(error)")
                }
                completion(accounts)
            }
        }

        return await withCheckedContinuation { continuation in
            dispatch { accounts in
                continuation.resume(returning: accounts)
            }
        }
    }

    private func fetchActiveAccountId() async -> String? {
        func dispatch(completion: @escaping (String?) -> Void) {
            DispatchQueue.global(qos: .background).async {
                var activeAccountId: String?
                do {
                    activeAccountId = try self.core.activeAccountId()
                } catch {
                    print("Error fetching active account id: \(error)")
                }
                completion(activeAccountId)
            }
        }

        return await withCheckedContinuation { continuation in
            dispatch { activeAccountId in
                continuation.resume(returning: activeAccountId)
            }
        }
    }

    func refreshAccounts() async {
        self.accounts = await self.listAccounts()
        self.activeAccountId = await self.fetchActiveAccountId()
    }
}

// MARK: - Account & Address

extension ViewModel {
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

    extension ViewModel {
        static func buildForPreview() -> ViewModel {
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

            return ViewModel(core: core, accounts: accounts, activeAccountId: "1")
        }
    }
#endif
