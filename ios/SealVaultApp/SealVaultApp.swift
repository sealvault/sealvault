// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

@main
struct SealVaultApp: SwiftUI.App {
    @State var isDoneRestoring = false

    var body: some Scene {
        WindowGroup {
            if !isDoneRestoring, let recoveryModel = GlobalModel.shouldRestoreBackup() {
                RecoveryView(isDoneRestoring: $isDoneRestoring, recoveryModel: recoveryModel)
            } else {
                AppInner()
            }
        }
    }
}

struct AppInner: View {
    @Environment(\.scenePhase) var scenePhase

    @StateObject private var model = GlobalModel.buildOnStartup()
    @StateObject private var bannerModel = BannerModel()

    var body: some View {
        AppTabNavigation()
            .environmentObject(model)
            .environmentObject(bannerModel)
            .task {
                // We aren't fetching dapp icons here because that'd make blocking
                // network requests and we want to show profiles asap on startup.
                await model.refreshProfiles(fetchDappIcons: false)

                #if DEBUG
                if CommandLine.arguments.contains(Config.createProfileArg) {
                    if !model.profileList.contains(where: { $0.name == Config.cliProfileName}) {
                        if let picName = await model.randomBundledProfilePicture() {
                            _ = await model.createProfile(name: Config.cliProfileName, bundledProfilePic: picName)
                        }
                    }
                }

                if CommandLine.arguments.contains(Config.triggerBanners) {
                    bannerModel.triggerBanners()
                }
                #endif
            }
            .onBackground {
                model.onBackground()
            }
    }
}
