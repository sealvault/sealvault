// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation

class RestoreModel: ObservableObject {
    @Published var backupDate: Date
    @Published var backupDeviceName: String
    let backupFilePath: String

    init(backupDate: Date, backupDeviceName: String, backupFilePath: String) {
        self.backupDate = backupDate
        self.backupDeviceName = backupDeviceName
        self.backupFilePath = backupFilePath
    }
}
