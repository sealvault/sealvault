// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation

// Injected to Rust through FFI for backup file storage operations
class CoreBackupStorage {
    // Example file name for files not yet downloaded from iCloud:
    // ".sealvault_backup_v1_ios_1672054688_B92B17B9-24A0-48FC-9709-281B15639BD8_2.zip.icloud"
    private static let  placeholderPrefix: String = "."
    private static let placeholderSuffix: String = ".icloud"

    // Canonical URL for items in iCloud which may have an ".icloud" suffix.
    private static func canonicalURL(_ url: URL) -> URL {
        let prefix = CoreBackupStorage.placeholderPrefix
        let suff = CoreBackupStorage.placeholderSuffix
        var fileName = url.lastPathComponent
        if fileName.hasPrefix(prefix), fileName.hasSuffix(suff) {
            fileName.removeFirst(prefix.count)
            fileName.removeLast(suff.count)
            var result = url.deletingLastPathComponent()
            result.append(path: fileName)
            return result
        } else {
            return url
        }
    }

    private static func backupFileURL(backupFileName: String) -> URL? {
        guard let backupDir = LocalFiles.ensureBackupDir() else {
            return nil
        }
        return backupDir.appending(path: backupFileName)
    }

    static func backupDirExists() -> Bool {
        guard let backupDir = LocalFiles.ensureBackupDir() else {
            return false
        }

        return FileManager.default.fileExists(atPath: backupDir.path)
    }
}

extension CoreBackupStorage: CoreBackupStorageI {
    func canBackup() -> Bool {
        FileManager.default.ubiquityIdentityToken != nil
    }

    func listBackupFileNames() -> [String] {
        var results = [String]()

        guard let backupDir = LocalFiles.backupDirURL() else {
            return results
        }

        let fileCoordinator = NSFileCoordinator(filePresenter: nil)
        fileCoordinator.coordinate(
            readingItemAt: backupDir,
            options: NSFileCoordinator.ReadingOptions(),
            error: nil
        ) { readingURL in
            do {
                let contents = try FileManager.default.contentsOfDirectory(
                    at: readingURL, includingPropertiesForKeys: nil
                )
                for url in contents {
                    let canonicalURL = CoreBackupStorage.canonicalURL(url)
                    results.append(canonicalURL.lastPathComponent)
                }
            } catch {
                print("Error listing backup files: '\(error)'")
            }
        }

        return results
    }

    func copyToStorage(backupFileName: String, tmpFilePath: String) -> Bool {
        let sourceURL = URL(filePath: tmpFilePath)

        guard let destinationURL = CoreBackupStorage.backupFileURL(backupFileName: backupFileName) else {
            return false
        }

        do {
            try FileManager.default.setUbiquitous(true, itemAt: sourceURL, destinationURL: destinationURL)
            return true
        } catch {
            print("Error deleting backup file: '\(error)'")
            return false
        }
    }

    func copyFromStorage(backupFileName: String, tmpFilePath: String) -> Bool {
        guard let sourceURL = CoreBackupStorage.backupFileURL(backupFileName: backupFileName) else {
            return false
        }

        let toURL = URL(filePath: tmpFilePath)

        let fileCoordinator = NSFileCoordinator(filePresenter: nil)
        var success = false
        fileCoordinator.coordinate(
            readingItemAt: sourceURL,
            options: NSFileCoordinator.ReadingOptions(),
            error: nil
        ) { readingURL in
            do {
                try FileManager.default.copyItem(at: readingURL, to: toURL)
                success = true
            } catch {
                print("Error copying backup file: '\(error)'")
            }
        }
        return success
    }

    func deleteBackup(backupFileName: String) -> Bool {
        guard let url = CoreBackupStorage.backupFileURL(backupFileName: backupFileName) else {
            return false
        }

        let fileCoordinator = NSFileCoordinator(filePresenter: nil)
        var success = false
        fileCoordinator.coordinate(
            writingItemAt: url,
            options: NSFileCoordinator.WritingOptions.forDeleting,
            error: nil
        ) { writingURL in
            do {
                try FileManager.default.removeItem(at: writingURL)
                success = true
            } catch {
                print("Error deleting backup file: '\(error)'")
            }
        }
        return success
    }
}
