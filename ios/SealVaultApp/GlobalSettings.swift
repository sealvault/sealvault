// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation
import SwiftUI

struct GlobalSettings: View {
    @EnvironmentObject private var model: GlobalModel

    var body: some View {
        VStack {
            List {
                Section("Device Backup") {
                    NavigationLink {
                        BackupSettings(backupEnabledToggle: model.backupEnabled)
                    } label: {
                        BackupSettingsRow()
                    }
                }
            }
        }
        .navigationTitle("Settings")
    }

}

struct BackupSettingsRow: View {
    @EnvironmentObject private var model: GlobalModel

    var stateText: String {
        model.backupEnabled ? "On" : "Off"
    }

    var body: some View {
        HStack {
            BackupSettingsLabel()
            Spacer()
            Text(stateText)
                .font(.callout)
        }
    }
}

struct BackupSettingsLabel: View {
    @EnvironmentObject private var model: GlobalModel

    var iconName: String {
        model.backupEnabled ? "checkmark.icloud":  "xmark.icloud"
    }

    var iconColor: Color {
        model.backupEnabled ?.green : .red
    }

    var body: some View {
        Label {
            Text("iCloud Storage Backup")
        } icon: {
            Image(systemName: iconName)
                .foregroundColor(iconColor)
        }
    }
}

#if DEBUG
struct GlobalSettings_Previews: PreviewProvider {
    static var previews: some View {
        Group {
            GlobalSettings()
                .environmentObject(GlobalModel.buildForPreview())
            GlobalSettings()
                .environmentObject(GlobalModel.buildForPreview())
                .preferredColorScheme(.dark)
        }
    }
}
#endif
