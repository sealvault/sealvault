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
        guard let backupDir = CoreBackupStorage.ensureBackupDir() else {
            return nil
        }
        return backupDir.appending(path: backupFileName)
    }

    static func backupDirURL() -> URL? {
        let driveURL = FileManager
            .default
            .url(forUbiquityContainerIdentifier: nil)?
            .appendingPathComponent(Config.iCloudBackupDirName)
        return driveURL
    }

    static func ensureBackupDir() -> URL? {
        guard let backupDir = CoreBackupStorage.backupDirURL()  else {
            return nil
        }

        let fileCoordinator = NSFileCoordinator(filePresenter: nil)
        var success = false
        fileCoordinator.coordinate(
            writingItemAt: backupDir,
            options: NSFileCoordinator.WritingOptions(),
            error: nil
        ) { dirURL in
            let fileManager = FileManager.default

            if !fileManager.fileExists(atPath: dirURL.path) {
                do {
                    try fileManager.createDirectory(
                        at: dirURL,
                        withIntermediateDirectories: true,
                        attributes: LocalFiles.dataProtectionAttributes()
                    )
                    let resourceValues = try dirURL.resourceValues(forKeys: [URLResourceKey.isUbiquitousItemKey])
                    if resourceValues.isUbiquitousItem != true {
                        print("Error: backup directory is not ubiquitous")
                        success = false
                    } else {
                        success = true
                    }
                } catch {
                    print("Failed to create backup dir with error: \(error)")
                }
            } else {
                success = true
            }
        }
        if success {
            return backupDir
        } else {
            return nil
        }
    }

    static func backupDirExists() -> Bool {
        guard let backupDir = CoreBackupStorage.ensureBackupDir() else {
            return false
        }

        return FileManager.default.fileExists(atPath: backupDir.path)
    }

    static func debugInfo() -> [BackupDebugInfo] {
        var results = [BackupDebugInfo]()
        guard let backupDir = CoreBackupStorage.backupDirURL() else {
            return results
        }
        let dirCoordinator = NSFileCoordinator(filePresenter: nil)
        dirCoordinator.coordinate(
            readingItemAt: backupDir,
            options: NSFileCoordinator.ReadingOptions(),
            error: nil
        ) { dirURL in
            do {
                let contents = try FileManager.default.contentsOfDirectory(
                    at: dirURL, includingPropertiesForKeys: nil
                )
                results.append(debugInfoForUrl(dirURL))

                for url in contents {
                    let fileCoordinator = NSFileCoordinator(filePresenter: nil)
                    fileCoordinator.coordinate(
                        readingItemAt: url,
                        options: NSFileCoordinator.ReadingOptions(),
                        error: nil
                    ) { fileURL in
                        results.append(debugInfoForUrl(fileURL))
                    }
                }
            } catch {
                print("Error listing backup files: '\(error)'")
            }
        }
        return results
    }

    private static func debugInfoForUrl(_ url: URL) -> BackupDebugInfo {
        var attributes = [String: String]()
        do {
            let values = try url.resourceValues(forKeys: Set(BackupDebugInfo.keys.keys))
            for (key, display) in BackupDebugInfo.keys {
                let value = values.allValues[key]
                attributes[display] = "\(value ?? "<None>")"
            }
            print(values)
        } catch {
            print("Error retrieving url resource values: \(error)")
        }

        return BackupDebugInfo(path: url.path, attributes: attributes)
    }
}

extension CoreBackupStorage: CoreBackupStorageI {
    func canBackup() -> Bool {
        FileManager.default.ubiquityIdentityToken != nil
    }

    func isUploaded(backupFileName: String) -> Bool {
        var result = false

        guard let fileURL = CoreBackupStorage.backupFileURL(backupFileName: backupFileName) else {
            return result
        }

        let fileCoordinator = NSFileCoordinator(filePresenter: nil)
        fileCoordinator.coordinate(
            readingItemAt: fileURL,
            options: NSFileCoordinator.ReadingOptions(),
            error: nil
        ) { readingURL in
            do {
                let resourceValues = try readingURL.resourceValues(
                    forKeys: [URLResourceKey.ubiquitousItemIsUploadedKey]
                )
                result = resourceValues.ubiquitousItemIsUploaded == true
            } catch {
                print("Error fetching isUploaded: '\(error)'")
            }
        }

        return result
    }

    func listBackupFileNames() -> [String] {
        var results = [String]()

        guard let backupDir = CoreBackupStorage.backupDirURL() else {
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
        guard let destinationURL = CoreBackupStorage.backupFileURL(backupFileName: backupFileName) else {
            return false
        }

        let sourceURL = URL(filePath: tmpFilePath)

        let fileCoordinator = NSFileCoordinator(filePresenter: nil)
        var success = false
        fileCoordinator.coordinate(
            writingItemAt: destinationURL,
            options: NSFileCoordinator.WritingOptions(),
            error: nil
        ) { writingURL in
            do {
                try FileManager.default.setUbiquitous(true, itemAt: sourceURL, destinationURL: writingURL)
                success = true
            } catch {
                print("Error moving backup file to storage: '\(error)'")
            }
        }
        return success
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

struct BackupDebugInfo {
    static let keys: [URLResourceKey: String] = [
        URLResourceKey.isDirectoryKey: "isDir",
        URLResourceKey.fileProtectionKey: "fileProt",
        URLResourceKey.isUbiquitousItemKey: "isUbiq",
        URLResourceKey.ubiquitousItemIsExcludedFromSyncKey: "excludedFromSync",
        URLResourceKey.ubiquitousItemIsUploadedKey: "isUploaded",
        URLResourceKey.ubiquitousItemIsUploadingKey: "isUploading",
        URLResourceKey.ubiquitousItemUploadingErrorKey: "uploadingError",
        URLResourceKey.ubiquitousItemHasUnresolvedConflictsKey: "unresolvedConflicts"
    ]

    var path: String
    var attributes: [
        String: String
    ]
}

extension BackupDebugInfo: Identifiable {
    var id: String {
        self.path
    }
}
