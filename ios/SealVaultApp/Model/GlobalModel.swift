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
    @Published var leftBrowserURL: URL?
    @Published var rightBrowserURL: URL?
    @Published var topDapps: [Dapp]
    // True by default to avoid showing warning while data is loading
    @Published var backupEnabled: Bool = true

    private var backgroundTaskID: UIBackgroundTaskIdentifier?

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

    static func coreArgs() -> CoreArgs {
        CoreArgs(
            deviceId: deviceId(), deviceName: deviceName(), cacheDir: LocalFiles.cacheDir(),
            dbFilePath: LocalFiles.ensureDbFilePath()
        )
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

    static func buildOnStartup() -> Self {
        let coreArgs = coreArgs()
        let callbackModel = CallbackModel()
        var core: AppCoreProtocol
        do {
            core = try AppCore(
                args: coreArgs, backupStorage: CoreBackupStorage(), uiCallback: CoreUICallback(callbackModel)
            )
        } catch {
            print("Failed to create core: \(error)")
            exit(1)
        }
        return Self(core: core, profiles: [], activeProfileId: nil, callbackModel: callbackModel)
    }

    static func shouldRestoreBackup() -> RecoveryModel? {
        let dbPath = LocalFiles.dbFilePath()
        // If we already have a db then we don't restore
        if FileManager.default.fileExists(atPath: dbPath.path) {
            return nil
        }

        let backupStorage = CoreBackupStorage()

        // If the backup directory is not available, because the user is not logged in to iCloud,
        // then we don't restore.
        if backupStorage.canBackup() {
            // If the backup directory doesn't exist, the user hasn't installed the app before, so
            // we don't restore.
            if !CoreBackupStorage.backupDirExists() {
                return nil
            }

            return RecoveryModel()
        }
        return nil
    }

}

// MARK: - App Core
extension GlobalModel {
    func onBackground() {
        DispatchQueue.global(qos: .background).async {
            // Request the task assertion and save the ID.
            DispatchQueue.main.sync {
                self.backgroundTaskID = UIApplication.shared.beginBackgroundTask(withName: "App Core On Background") {
                    // End the task if time expires.
                    UIApplication.shared.endBackgroundTask(self.backgroundTaskID!)
                    self.backgroundTaskID = UIBackgroundTaskIdentifier.invalid
                }
            }

            do {
                try self.core.onBackground()
            } catch {
                print("Error for core onBackground: \(error)")
            }

            // End the task assertion.
            DispatchQueue.main.sync {
                UIApplication.shared.endBackgroundTask(self.backgroundTaskID!)
                self.backgroundTaskID = UIBackgroundTaskIdentifier.invalid
            }
        }
    }

    private func listProfiles(_ qos: DispatchQoS.QoSClass, fetchDappIcons: Bool) async -> [CoreProfile]? {
        return await dispatchBackground(qos) {
            do {
                return try self.core.listProfiles(fetchDappIcons: fetchDappIcons)
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

    func setActiveProfileId(profileId: String) async -> BannerData? {
        let errorMessage: String? = await dispatchBackground(.userInteractive) {
            do {
                try self.core.setActiveProfileId(profileId: profileId)
                return nil
            } catch CoreError.Retriable(let message) {
                print("Retriable error changing active profile: \(message)")
                return Config.retriableErrorMessage
            } catch let error {
                print("Fatal error changing active profile: \(error)")
                return Config.fatalErrorMessage
            }
        }
        if let message = errorMessage {
            return BannerData(
                title: "Error changing active profile",
                detail: message,
                type: .error
            )
        } else {
            await self.refreshProfiles()
            return nil
        }
    }

    func launchInBrowser(_ browser: BrowserWindow, profile: Profile, url: URL) async -> BannerData? {
        var res: BannerData?
        if activeProfileId != profile.id {
            res = await setActiveProfileId(profileId: profile.id)
        }
        switch browser {
        case .left:
            leftBrowserURL = url
        case .right:
            rightBrowserURL = url
        }
        return res
    }

    func enableBackup() async -> BannerData? {
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
            return nil
        } else {
            return BannerData(
                title: "Error enabling backup",
                detail: "Make sure iCloud is enabled and try to restart the app.",
                type: .error
            )
        }
    }

    func disableBackup() async -> BannerData? {
        let success = await dispatchBackground(.userInteractive) {
            do {
                try self.core.disableBackup()
                return true
            } catch {
                print("Error enabling backup: \(error)")
                return false
            }
        }
        if success {
            self.backupEnabled = await self.fetchBackupEnabled()
            return nil
        } else {
            return BannerData(
                title: "Error disabling backup", detail: "", type: .error
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
        return await dispatchBackground(.userInteractive) {
            do {
                return try self.core.isBackupEnabled()
            } catch {
                print("Error fetching whether backup is enabled: \(error)")
                return false
            }
        }
    }

    func fetchLastBackup() async -> Date? {
        return await dispatchBackground(.userInteractive) {
            do {
                if let lastBackup = try self.core.lastUploadedBackup() {
                    return Date(timeIntervalSince1970: Double(lastBackup))
                } else {
                    return nil
                }
            } catch {
                print("Error fetching last backup: \(error)")
                return nil
            }
        }
    }

    func tabBarColor(_ colorScheme: ColorScheme) -> Color {
        colorScheme == .dark ? .black : Color(UIColor.systemGray6)
    }

    func refreshProfiles(fetchDappIcons: Bool = true) async {
        let profiles = await self.listProfiles(.userInteractive, fetchDappIcons: fetchDappIcons)
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

    func randomBundledProfilePicture() async -> String? {
        return await dispatchBackground(.userInteractive) {
            do {
                return try self.core.randomBundledProfilePicture()
            } catch {
                print("Error fetching profile name: \(error)")
                return nil
            }
        }
    }

    func fetchBundledProfilePicture(pictureName: String) async -> [UInt8]? {
        return await dispatchBackground(.userInteractive) {
            do {
                return try self.core.fetchBundledProfilePicture(pictureName: pictureName)
            } catch {
                print("Error fetching profile picture: \(error)")
                return nil
            }
        }
    }

    func createProfile(name: String, bundledProfilePic: String) async -> BannerData? {
        let errorMessage: String? = await dispatchBackground(.userInteractive) {
            do {
                try self.core.createProfile(name: name, bundledPictureName: bundledProfilePic)
                return nil
            } catch CoreError.User(let message) {
                return message
            } catch CoreError.Retriable(let message) {
                print("Retriable error creating profile: \(message)")
                return Config.retriableErrorMessage
            } catch let error {
                print("Fatal error creating profile: \(error)")
                return Config.fatalErrorMessage
            }
        }
        if let message = errorMessage {
            return BannerData(
                title: "Error creating profile",
                detail: message,
                type: .error
            )
        } else {
            await self.refreshProfiles()
            return nil
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
import SwiftUI

// swiftlint:disable force_try
/// The App Core is quite heavy as it runs migrations etc on startup, and we don't need it for preview, so we just
/// pass this stub.
class PreviewAppCore: AppCoreProtocol {
    func fetchAddress(addressId: String) throws -> CoreAddress {
        Self.toCoreAddress(Address.polygonDapp())
    }

    func tokensForEthAddress(checksumAddress: String) throws -> [CoreTokens] {
        [try! self.tokensForAddressId(addressId: checksumAddress)]
    }

    func tokensForAddressId(addressId: String) throws -> CoreTokens {
        CoreTokens(
            addressId: addressId,
            nativeToken: try! self.nativeTokenForAddress(addressId: addressId),
            fungibleTokens: try! self.fungibleTokensForAddress(addressId: addressId),
            nfts: [Self.toCoreNFT(NFT.example())]
        )
    }

    private var backupEnabledToggle: Bool = true

    static func toCoreProfile(_ profile: Profile) -> CoreProfile {
        let picture = [UInt8](profile.picture.pngData()!)
        let wallets = profile.wallets.addressList.map(Self.toCoreAddress)
        let dapps = profile.dappList.map(Self.toCoreDapp)
        return CoreProfile(
            id: profile.id, name: profile.name, picture: picture, wallets: wallets, dapps: dapps,
            createdAt: "2022-08-01", updatedAt: "2022-08-01"
        )
    }

    static func toCoreDapp(_ dapp: Dapp) -> CoreDapp {
        let icon = dapp.favicon.map { [UInt8]($0.pngData()!) }
        let url = dapp.url?.absoluteString ?? "https://ens.domains"
        let addresses = dapp.addresses.addressList.map(Self.toCoreAddress)

        return CoreDapp(
            id: dapp.id, profileId: dapp.profileId, humanIdentifier: dapp.humanIdentifier, url: url,
            addresses: addresses, selectedAddressId: dapp.selectedAddressId, favicon: icon, lastUsed: dapp.lastUsed
        )
    }

    static func toCoreAddress(_ address: Address) -> CoreAddress {
        let nativeToken = Self.toCoreToken(address.nativeToken)
        let blockchainExplorerLink = address.blockchainExplorerLink?.absoluteString ?? "https://etherscani.io"
        return CoreAddress(
            id: address.id, isWallet: address.isWallet, checksumAddress: address.checksumAddress,
            blockchainExplorerLink: blockchainExplorerLink, chain: address.chain, nativeToken: nativeToken
        )
    }

    static func toCoreToken(_ token: Token) -> CoreFungibleToken {
        let icon = [UInt8](token.icon.pngData()!)
        return CoreFungibleToken(
            id: token.id,
            symbol: token.symbol,
            amount: token.amount,
            tokenType: FungibleTokenType.native,
            icon: icon
        )
    }

    static func toCoreNFT(_ nft: NFT) -> CoreNft {
        return CoreNft(id: nft.id, displayName: nft.displayName)
    }

    private func fungibleTokensForAddress(addressId: String) throws -> [CoreFungibleToken] {
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

    private func nativeTokenForAddress(addressId: String) throws -> CoreFungibleToken {
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

    func onBackground() throws {
        print("on background starting")
        // Simulate creating backup
        Thread.sleep(forTimeInterval: 1)
        print("on background finished")
    }

    func enableBackup() throws {
        // Simulate password KDF
        Thread.sleep(forTimeInterval: 1)
        self.backupEnabledToggle = true
    }

    func disableBackup() throws {
        Thread.sleep(forTimeInterval: 0.5)
        backupEnabledToggle = false
    }

    func isBackupEnabled() throws -> Bool {
        self.backupEnabledToggle
    }

    func lastUploadedBackup() throws -> Int64? {
        Thread.sleep(forTimeInterval: 0.5)
        return Int64(Date().timeIntervalSince1970)
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

    func listProfiles(fetchDappIcons _: Bool) throws -> [CoreProfile] {
        let wallets = [
            Address.ethereumWallet(),
            Address.polygonWallet()
        ]
        let activeProfileName = "alice.eth"
        let activeProfileId = try! self.activeProfileId()

        let profiles = [
            Profile(
                self,
                id: activeProfileId, name: activeProfileName, picture: UIImage(named: "seal-7")!,
                wallets: wallets,
                dapps: [
                    Dapp.ens(),
                    Dapp.opensea(),
                    Dapp.uniswap(),
                    Dapp.sushi(),
                    Dapp.aave(),
                    Dapp.oneInch(),
                    Dapp.quickswap(),
                    Dapp.darkForest(),
                    Dapp.dnd(),
                    Dapp.lilNouns()
                ]
            ),
            Profile(
                self,
                id: "2", name: "DeFi Anon", picture: UIImage(named: "seal-1")!, wallets: wallets,
                dapps: [Dapp.dhedge(), Dapp.sushi(), Dapp.aave(), Dapp.oneInch(), Dapp.quickswap(), Dapp.uniswap()]
            ),
            Profile(
                self,
                id: "3", name: "Dark Forest Commander", picture: UIImage(named: "seal-2")!, wallets: wallets,
                dapps: [Dapp.darkForest()]
            ),
            Profile(
                self,
                id: "5", name: "NSFW", picture: UIImage(named: "seal-6")!, wallets: wallets,
                dapps: [Dapp.xmpt()]
            ),
            Profile(
                self,
                id: "6", name: "Vacation Mode", picture: UIImage(named: "seal-0")!, wallets: wallets,
                dapps: [Dapp.poap()]
            )
        ]

        return profiles.map(Self.toCoreProfile)
    }

    func createProfile(name: String, bundledPictureName: String) throws {
        throw CoreError.Fatal(message: "not implemented")
    }

    func randomBundledProfilePicture() throws -> String? {
        "seal-9"
    }

    func fetchBundledProfilePicture(pictureName: String) throws -> [UInt8] {
        let name = try! randomBundledProfilePicture()
        return [UInt8](UIImage(named: name!)!.pngData()!)
    }

    func activeProfileId() throws -> String {
        return "1"
    }

    func setActiveProfileId(profileId: String) throws {
        throw CoreError.Fatal(message: "not implemented")
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
            Address.ethereumChain(),
            Address.goerliChain(),
            Address.polygonChain(),
            Address.mumbaiChain()
        ]
    }

    func topDapps(limit: UInt32) throws -> [String] {
        let res = try! listProfiles(fetchDappIcons: true).first!.dapps.map {$0.id}.prefix(Int(limit))
        return [String](res)
    }
}

extension GlobalModel {
    static func buildForPreview() -> GlobalModel {
        let core = PreviewAppCore()
        let profiles = try! core.listProfiles(fetchDappIcons: true).map { Profile.fromCore(core, $0) }
        let activeProfileId = try! core.activeProfileId()
        return GlobalModel(
            core: core, profiles: profiles, activeProfileId: activeProfileId, callbackModel: CallbackModel()
        )
    }
}
// swiftlint:enable force_try
#endif
