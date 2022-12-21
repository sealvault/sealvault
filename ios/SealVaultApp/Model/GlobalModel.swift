// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation
import SwiftUI

@MainActor
class GlobalModel: ObservableObject {
    @Published var profiles: [String: Profile]
    /// The profile currently used for dapp interactions
    @Published var activeProfileId: String?
    @Published var callbackModel: CallbackModel
    @Published var browserOneUrl: URL?
    @Published var browserTwoUrl: URL?
    @Published var topDapps: [Dapp]
    @Published var bannerData: BannerData?
    @Published var backupEnabled: Bool = false

    var activeProfile: Profile? {
        return profileList.first(where: { acc in acc.id == activeProfileId })
    }

    var profileList: [Profile] {
        profiles.values.sorted(by: {$0.displayName.lowercased() < $1.displayName.lowercased()})
    }

    let core: AppCoreProtocol

    required init(core: AppCoreProtocol, profiles: [Profile], activeProfileId: String?, callbackModel: CallbackModel) {
        self.core = core
        self.profiles = Dictionary(uniqueKeysWithValues: profiles.map { ($0.id, $0) })
        self.activeProfileId = activeProfileId
        self.callbackModel = callbackModel
        self.topDapps = []
    }

    private func updateProfiles(_ coreProfiles: [CoreProfile]) {
        let newIds = Set(coreProfiles.map {$0.id})
        let oldIds = Set(self.profiles.keys)
        let toRemoveIds = oldIds.subtracting(newIds)
        for id in toRemoveIds {
            self.profiles.removeValue(forKey: id)
        }
        for coreProfile in coreProfiles {
            if let profile = self.profiles[coreProfile.id] {
                profile.updateFromCore(coreProfile)
            } else {
                let profile = Profile.fromCore(self.core, coreProfile)
                self.profiles[profile.id] = profile
            }
        }
    }

    static func buildOnStartup() -> Self {
        let coreArgs = CoreArgs(
            deviceId: deviceId(), deviceName: deviceName(), cacheDir: cacheDir(),
            dbFilePath: ensureDbFilePath(), backupDir: backupDir()
        )
        let callbackModel = CallbackModel()
        var core: AppCoreProtocol
        do {
            core = try AppCore(args: coreArgs, uiCallback: CoreUICallback(callbackModel))
        } catch {
            print("Failed to create core: \(error)")
            exit(1)
        }
        return Self(core: core, profiles: [], activeProfileId: nil, callbackModel: callbackModel)
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

    private static func deviceName() -> String {
        UIDevice.current.name
    }

    private static func deviceId() -> String {
        // TODO
        // > If the value is nil, wait and get the value again later.
        // > This happens, for example, after the device has been restarted but before the
        // > user has unlocked the device.
        // https://developer.apple.com/documentation/uikit/uidevice/1620059-identifierforvendor
        UIDevice.current.identifierForVendor!.uuidString
    }

    private static func backupDir() -> String? {
        let driveURL = FileManager
            .default
            .url(forUbiquityContainerIdentifier: Config.backupContainerIdentifier)?
            .appendingPathComponent(Config.iCloudBackupDirName)

        return driveURL?.path
    }

    private func listProfiles(_ qos: DispatchQoS.QoSClass) async -> [CoreProfile]? {
        return await dispatchBackground(qos) {
            do {
                return try self.core.listProfiles()
            } catch {
                print("Error fetching profile data: \(error)")
                return nil
            }
        }
    }

    private func fetchActiveProfileId(_ qos: DispatchQoS.QoSClass) async -> String? {
        return await dispatchBackground(qos) {
            do {
                return try self.core.activeProfileId()
            } catch {
                print("Error fetching active profile id: \(error)")
                return nil
            }
        }
    }

    func enableBackup() async {
        let success = await dispatchBackground(.userInteractive) {
            do {
                try self.core.enableBackup()
                return true
            } catch {
                print("Error enabling backup: \(error)")
                return false
            }
        }
        if success {
            self.backupEnabled = await self.fetchBackupEnabled()
        } else {
            self.bannerData = BannerData(
                title: "Error enabling backup", detail: "Make sure iCloud is enabled.", type: .error
            )
        }
    }

    func displayBackupPassword() async -> String? {
        await dispatchBackground(.userInteractive) {
            do {
                return try self.core.displayBackupPassword()
            } catch {
                print("Error enabling backup: \(error)")
                return nil
            }
        }
    }

    func fetchBackupEnabled() async -> Bool {
        do {
            return try self.core.isBackupEnabled()
        } catch {
            print("Error fetching whether backup is enabled: \(error)")
            return false
        }
    }

    func tabBarColor(_ colorScheme: ColorScheme) -> Color {
        colorScheme == .dark ? .black : Color(UIColor.systemGray6)
    }

    func refreshProfiles() async {
        let profiles = await self.listProfiles(.userInteractive)
        let activeProfileId = await self.fetchActiveProfileId(.userInteractive)

        if let profiles = profiles {
            self.updateProfiles(profiles)
        }
        if let activeProfileId = activeProfileId {
            self.activeProfileId = activeProfileId
        }
        self.backupEnabled = await self.fetchBackupEnabled()
        self.topDapps = await self.fetchTopDapps(limit: Config.topDappsLimit)
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
        await self.refreshProfiles()
    }

    func changeDappChain(profileId: String, dappId: String, newChainId: UInt64) async {
        await dispatchBackground(.userInteractive) {
            do {
                let args = EthChangeDappChainArgs(profileId: profileId, dappId: dappId, newChainId: newChainId)
                try self.core.ethChangeDappChain(args: args)
            } catch {
                print("Error changing dapp address for dapp: \(error)")
            }
        }
        // Make sure newly added chain shows up
        await self.refreshProfiles()
    }

    func listEthChains() async -> [CoreEthChain] {
        return await dispatchBackground(.userInteractive) {
            self.core.listEthChains()
        }
    }

    func fetchTopDapps(limit: Int) async -> [Dapp] {
        let topDappIds = await dispatchBackground(.userInteractive) {
            do {
                return try self.core.topDapps(limit: UInt32(limit))
            } catch {
                print("Error listing top dapps: \(error)")
                return []
            }
        }
        return activeProfile?.dappList.filter { topDappIds.contains($0.id) } ?? []
    }
}

// MARK: - Development

#if DEBUG
// swiftlint:disable force_try
import SwiftUI
/// The App Core is quite heavy as it runs migrations etc on startup, and we don't need it for preview, so we just
/// pass this stub.
class PreviewAppCore: AppCoreProtocol {
    private var backupEnabled: Bool = false

    static func toCoreProfile(_ profile: Profile) -> CoreProfile {
        let picture = [UInt8](profile.picture.pngData()!)
        let wallets = profile.walletList.map(Self.toCoreAddress)
        let dapps = profile.dappList.map(Self.toCoreDapp)
        return CoreProfile(
            id: profile.id, name: profile.name, picture: picture, wallets: wallets, dapps: dapps,
            createdAt: "2022-08-01", updatedAt: "2022-08-01"
        )
    }

    static func toCoreDapp(_ dapp: Dapp) -> CoreDapp {
        let icon = [UInt8](dapp.favicon.pngData()!)
        let url = dapp.url?.absoluteString ?? "https://ens.domains"
        let addresses = dapp.addressList.map(Self.toCoreAddress)

        return CoreDapp(
            id: dapp.id, profileId: dapp.profileId, humanIdentifier: dapp.humanIdentifier, url: url,
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
            if addressId.contains("ETH") {
                // Force update with new ids
                return [Token.dai(UUID().uuidString), Token.usdc(UUID().uuidString)]
            } else {
                return [Token.busd(UUID().uuidString)]
            }
        }
        Thread.sleep(forTimeInterval: 1)
        return DispatchQueue.main.sync {
            return tokens.map(Self.toCoreToken)
        }
    }

    func nativeTokenForAddress(addressId: String) throws -> CoreToken {
        let token = DispatchQueue.main.sync {
            if addressId.contains("ETH") {
                // Force update with new ids
                return Token.eth(UUID().uuidString)
            } else {
                return Token.matic(UUID().uuidString)
            }
        }
        Thread.sleep(forTimeInterval: 1)
        return DispatchQueue.main.sync {
            return Self.toCoreToken(token)
        }
    }

    func enableBackup() throws {
        // Simulate password KDF
        Thread.sleep(forTimeInterval: 1)
        self.backupEnabled = true
    }

    func isBackupEnabled() throws -> Bool {
        self.backupEnabled
    }

    func displayBackupPassword() throws -> String {
        "AAA1-BBB2-CCC3-DDD4"
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

    func listProfiles() throws -> [CoreProfile] {
        let wallets = [
            Address.ethereumWallet(),
            Address.polygonWallet()
        ]
        let activeProfileName = "alice.eth"
        let activeProfileId = try! self.activeProfileId()

        let profiles = [
            Profile(
                self,
                id: activeProfileId, name: activeProfileName, picture: UIImage(named: "cat-green")!,
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
            Profile(
                self,
                id: "2", name: "DeFi Anon", picture: UIImage(named: "orangutan")!, wallets: wallets,
                dapps: [Dapp.dhedge(), Dapp.sushi(), Dapp.aave(), Dapp.oneInch(), Dapp.quickswap(), Dapp.uniswap()]
            ),
            Profile(
                self,
                id: "3", name: "Dark Forest General", picture: UIImage(named: "owl-chatty")!, wallets: wallets,
                dapps: [Dapp.darkForest()]
            ),
            Profile(
                self,
                id: "4", name: "D&D Magician", picture: UIImage(named: "dog-derp")!, wallets: wallets,
                dapps: [Dapp.dnd()]
            ),
            Profile(
                self,
                id: "5", name: "NSFW", picture: UIImage(named: "dog-pink")!, wallets: wallets,
                dapps: [Dapp.opensea()]
            )
        ]

        return profiles.map(Self.toCoreProfile)
    }

    func activeProfileId() throws -> String {
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

    func topDapps(limit: UInt32) throws -> [String] {
        let res = try! listProfiles().first!.dapps.map {$0.id}.prefix(Int(limit))
        return [String](res)
    }
}

extension GlobalModel {
    static func buildForPreview() -> GlobalModel {
        let core = PreviewAppCore()
        let profiles = try! core.listProfiles().map { Profile.fromCore(core, $0) }
        let activeProfileId = try! core.activeProfileId()
        return GlobalModel(
            core: core, profiles: profiles, activeProfileId: activeProfileId, callbackModel: CallbackModel()
        )
    }
}
// swiftlint:enable force_try
#endif
