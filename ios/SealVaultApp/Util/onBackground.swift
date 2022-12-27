// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

// Based on https://stackoverflow.com/a/72177271
extension View {
    #if os(iOS)
    func onBackground(_ callback: @escaping () -> Void) -> some View {
        self.onReceive(
            NotificationCenter.default.publisher(for: UIApplication.didEnterBackgroundNotification),
            perform: { _ in callback() }
        )
    }
    #else
    func onBackground(_ callback: @escaping () -> Void) -> some View {
        self.onReceive(
            NotificationCenter.default.publisher(for: NSApplication.didEnterBackgroundNotification),
            perform: { _ in callback() }
        )
    }
    #endif
}
