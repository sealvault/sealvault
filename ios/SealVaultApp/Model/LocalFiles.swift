// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation

class LocalFiles {
    static func dbDirPath() -> URL {
        let documentsURL = FileManager.default.urls(for: .documentDirectory, in: .userDomainMask).first!
        let dbDirPath = documentsURL.appendingPathComponent(Config.dbFileDir)
        return dbDirPath
    }

    static func dbFilePath() -> URL {
        dbDirPath().appendingPathComponent(Config.dbFileName)
    }

    static func dataProtectionAttributes() -> [FileAttributeKey: Any] {
        return [
            FileAttributeKey.protectionKey: FileProtectionType.completeUntilFirstUserAuthentication
        ]
    }

    static func ensureDbFilePath() -> String {
        let fileManager = FileManager.default

        let dirPath = dbDirPath()
        if !fileManager.fileExists(atPath: dirPath.path) {
            // App can't start if it can't create this directory
            // swiftlint:disable force_try
            try! fileManager.createDirectory(
                atPath: dirPath.path, withIntermediateDirectories: true, attributes: dataProtectionAttributes()
            )
            // swiftlint:enable force_try
        }

        var dbFilePath = dbFilePath()
        if !fileManager.fileExists(atPath: dbFilePath.path) {
            fileManager.createFile(atPath: dbFilePath.path, contents: nil, attributes: dataProtectionAttributes())
        }

        // Exclude DB file from iCloud Backup since it won't work due to missing keys from local keychain
        // More info https://sealvault.org/dev-docs/design/backup/#icloud-device-backup
        if var resourceValues = try? dbFilePath.resourceValues(forKeys: [URLResourceKey.isExcludedFromBackupKey]) {
            if resourceValues.isExcludedFromBackup != true {
                resourceValues.isExcludedFromBackup = true
                try? dbFilePath.setResourceValues(resourceValues)
            }
        }

        return dbFilePath.path
    }

    static func cacheDir() -> String {
        let fileManager = FileManager.default
        let cacheDirUrl = fileManager.urls(for: .cachesDirectory, in: .userDomainMask).first!

        return cacheDirUrl.path
    }

    static func backupDirURL() -> URL? {
        let driveURL = FileManager
            .default
            .url(forUbiquityContainerIdentifier: nil)?
            .appendingPathComponent(Config.iCloudBackupDirName)
        return driveURL
    }

    static func ensureBackupDir() -> URL? {
        if let backupDir = LocalFiles.backupDirURL() {
            let fileManager = FileManager.default

            if !fileManager.fileExists(atPath: backupDir.path) {
                do {
                    try fileManager.createDirectory(
                        at: backupDir, withIntermediateDirectories: true, attributes: dataProtectionAttributes()
                    )
                } catch {
                    print("Failed to create backup dir with error: \(error)")
                    return nil
                }

            }
            return backupDir
        }
        return nil
    }

}
