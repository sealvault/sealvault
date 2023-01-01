// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation
import SwiftUI

struct Config {
    // DB
    static let dbFileDir = "database"
    static let dbFileName = "sealvault-db.sqlite3"
    // Browser
    static let topDappsLimit = 5
    static let searchProvider = URL(string: "https://search.brave.com/search")!
    static let searchQueryParamName = "q"
    static let blankPageAddress = "about:blank"
    // There are two dapps by default
    static let showDisclosureDappCount = 7
    static let iCloudBackupDirName = "Backups"
    // Temporary until we let users add custom profile pics.
    static let maxProfiles = 10
    static let fatalErrorMessage = "An unexpected error occurred. Please restart the application!"
    static let retriableErrorMessage = "Something went wrong. Please try again!"
}

#if DEBUG
extension Config {
    // Create an additional profile on startup for UI testing
    static let createProfileArg = "-createProfile"
    static let cliProfileName = "CLI Profile"
}
#endif
