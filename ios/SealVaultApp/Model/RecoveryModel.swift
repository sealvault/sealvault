// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation
import SwiftUI

class RecoveryModel: ObservableObject {
    private static let timeout: Duration = .seconds(60)

    let backupDir: URL

    @Published var restoreData: RestoreModel?
    @Published var didFinish: Bool = false

    init(backupDir: URL, start: Bool = true) {
        self.backupDir = backupDir
        if start {
            self.start()
        }
    }

    static func buildForPreview() -> RecoveryModel {
        let documentsURL = FileManager.default.urls(for: .documentDirectory, in: .userDomainMask).first!
        let backupDir = documentsURL.appendingPathComponent(Config.iCloudBackupDirName)
        let model = RecoveryModel(backupDir: backupDir, start: false)
        return model
    }

    func start() {
        self.didFinish = false
        // iCloud doesn't automatically sync files to a new device, so we have to download them manually.
        self.downloadBackups()
    }

    private func downloadBackups() {
        Task {
            defer {
                DispatchQueue.main.sync {
                    withAnimation {
                        self.didFinish = true
                    }
                }
            }
            do {
                let downloadBackupDir = BackupDownloader(url: backupDir)
                try await downloadBackupDir.download()

                let contents = try FileManager.default.contentsOfDirectory(
                    at: backupDir, includingPropertiesForKeys: nil
                )
                for url in contents {
                    try Task.checkCancellation()
                    print(url)
                    let downloader = BackupDownloader(url: url)
                    try await downloader.download()
                }

                await self.findLatestBackup()
            } catch {
                print("Downloading backups failed with error: '\(error)'")
            }
        }
    }

    private func findLatestBackup() async {
        let maybeRestoreData = await dispatchBackground(.userInteractive, blockingCall: {
            do {
                return try coreFindLatestBackup(backupDir: self.backupDir.path)
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
    let backupFilePath: String

    init(backupDate: Date, backupDeviceName: String, backupFilePath: String) {
        self.backupDate = backupDate
        self.backupDeviceName = backupDeviceName
        self.backupFilePath = backupFilePath
    }

    convenience init(_ restoreData: BackupRestoreData) {
        let backupDate = Date(timeIntervalSince1970: Double(restoreData.timestamp))
        self.init(
            backupDate: backupDate, backupDeviceName: restoreData.deviceName, backupFilePath: restoreData.filePath
        )
    }
}

private enum DownloadError: Error {
    case timeout
}

// Download the backup directory or backup files from iCloud Storage
private actor BackupDownloader {
    // Example file name for files not yet downloaded from iCloud:
    // ".sealvault_backup_v1_ios_1672054688_B92B17B9-24A0-48FC-9709-281B15639BD8_2.zip.icloud"
    private static let  placeholderPrefix: String = "."
    private static let placeholderSuffix: String = ".icloud"

    private var url: URL
    private var polllURL: URL
    private let pollFrequency: Duration
    private let timeoutSeconds: Int

    init(url: URL, timeoutSeconds: Int = 15, pollFrequency: Duration = .milliseconds(500)) {
        self.url = url
        self.polllURL = BackupDownloader.pollURL(url)
        self.pollFrequency = pollFrequency
        self.timeoutSeconds = timeoutSeconds
    }

    // Poll for the actual URL not the placeholder, as the download status of the placeholder doesn't update.
    private static func pollURL(_ url: URL) -> URL {
        var fileName = url.lastPathComponent
        if fileName.hasPrefix(BackupDownloader.placeholderPrefix),
            fileName.hasSuffix(BackupDownloader.placeholderSuffix) {
            fileName.removeFirst(BackupDownloader.placeholderPrefix.count)
            fileName.removeLast(BackupDownloader.placeholderSuffix.count)
            var result = url.deletingLastPathComponent()
            result.append(path: fileName)
            return result
        } else {
            return url
        }
    }

    private func isDownloaded() -> Bool {
        // Important to clear cache otherwise we won't see updates after download
        polllURL.removeCachedResourceValue(forKey: URLResourceKey.ubiquitousItemDownloadingStatusKey)

        let attributes = try? polllURL.resourceValues(forKeys: [URLResourceKey.ubiquitousItemDownloadingStatusKey])
        if let status: URLUbiquitousItemDownloadingStatus = attributes?.allValues[
            URLResourceKey.ubiquitousItemDownloadingStatusKey] as? URLUbiquitousItemDownloadingStatus {
            return status == URLUbiquitousItemDownloadingStatus.current
        } else {
            return false
        }
    }

    // The notification observer approach didn't work, so we do polling.
    func download() async throws {
        if isDownloaded() {
            return
        }

        let startTime = DispatchTime.now()

        func hasTimedOut() -> Bool {
            let endTime = startTime.advanced(by: .seconds(timeoutSeconds))
            return endTime <= DispatchTime.now()
        }

        // Start the download
        try FileManager.default.startDownloadingUbiquitousItem(at: url)

        while !hasTimedOut() {
            try await Task.sleep(for: self.pollFrequency)

            if isDownloaded() {
                return
            }
        }
    }
}
