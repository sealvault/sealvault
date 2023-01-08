// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation
import SwiftUI

class RecoveryModel: ObservableObject {
    private static let timeout: Duration = .seconds(60)

    @Published var restoreData: RestoreModel?
    @Published var didFinish: Bool = false

    init(start: Bool = true) {
        if start {
            self.start()
        }
    }

    static func buildForPreview() -> RecoveryModel {
        let model = RecoveryModel(start: false)
        return model
    }

    func start() {
        self.didFinish = false
        Task {
            await findLatestBackup()
            DispatchQueue.main.async {
                self.didFinish = true
            }
        }
    }

    private func findLatestBackup() async {
        let maybeRestoreData = await dispatchBackground(.userInteractive, blockingCall: {
            do {
                return try coreFindLatestBackup(backupStorage: CoreBackupStorage())
            } catch {
                print("Error finding latest backup: \(error)")
                return nil
            }
        })
        DispatchQueue.main.sync {
            withAnimation {
                if let restoreData = maybeRestoreData {
                    self.restoreData = RestoreModel(restoreData)
                } else {
                    self.restoreData = nil
                }
            }
        }
    }
}

class RestoreModel: ObservableObject {
    @Published var backupDate: Date
    @Published var backupDeviceName: String
    let backupFileName: String

    init(backupDate: Date, backupDeviceName: String, backupFileName: String) {
        self.backupDate = backupDate
        self.backupDeviceName = backupDeviceName
        self.backupFileName = backupFileName
    }

    convenience init(_ restoreData: BackupRestoreData) {
        let backupDate = Date(timeIntervalSince1970: Double(restoreData.timestamp))
        self.init(
            backupDate: backupDate, backupDeviceName: restoreData.deviceName, backupFileName: restoreData.backupFileName
        )
    }
}
