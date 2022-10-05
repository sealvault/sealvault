// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

@main
struct SealVaultApp: SwiftUI.App {
    @ObservedObject private var model = GlobalModel.buildOnStartup()

    var body: some Scene {
        WindowGroup {
            AppTabNavigation()
                .environmentObject(model)
        }
    }
}
