// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation
import SwiftUI

struct BackupSettings: View {
    @EnvironmentObject private var model: GlobalModel
    @Environment(\.presentationMode) var presentationMode: Binding<PresentationMode>

    @State var backupEnabledToggle: Bool = false
    @State var presentConfirmation: Bool = false
    @State var wasOnboarding: Bool = false

    var body: some View {
        VStack {
            if !wasOnboarding && model.backupEnabled {
                Form {
                    Section {
                        Toggle(isOn: $backupEnabledToggle) {
                            BackupSettingsLabel()
                        }
                    } header: {
                        Text("Device Backup")
                    }

                    BackupSettingsInner()
                }
            } else {
                BackupSettingsOnboarding()
            }
        }
        .onChange(of: backupEnabledToggle) { newValue in
            if !newValue {
                presentConfirmation = true
            }
        }
        .onChange(of: model.backupEnabled) { newValue in
            if !newValue {
                // Go back in nav
                presentationMode.wrappedValue.dismiss()
            } else {
                backupEnabledToggle = newValue
                wasOnboarding = true
            }
        }
        .confirmationDialog("Are you sure you want to disable backups?", isPresented: $presentConfirmation) {
            Button("Disable Backups", role: .destructive, action: {
              Task {
                  await model.disableBackup()
              }
            })
            Button("Cancel", role: .cancel, action: {
                backupEnabledToggle = true
            })
        }
        .banner(data: $model.bannerData)
        .navigationTitle("iCloud Storage Backup")
        .navigationBarTitleDisplayMode(.inline)
    }
}

struct BackupSettingsOnboarding: View {
    @EnvironmentObject private var model: GlobalModel
    @Environment(\.colorScheme) private var colorScheme

    @State var step1: Bool = false
    @State var step2: Bool = false
    @State var step3: Bool = false
    @State var step4: Bool = false
    @State var step5: Bool = false

    var icloudSyncScreenshot: String {
        colorScheme == .dark ? "icloud-sync-setting-screenshot-dark" : "icloud-sync-setting-screenshot-light"
    }

    var body: some View {
        Form {
            Text(
"""
Automatically back up your keys and profiles to your iCloud Storage so that you can \
restore them if you lose your device or get a new one.
"""
            )
            .foregroundColor(step1 ? .secondary : .primary)

            if !step1 {
                Button("Enable Backups") {
                    withAnimation {
                        step1 = true
                    }
                }
            }

            if step1 {
                Text(
"""
All backups are encrypted with a strong backup password generated on your device. \
The backup password is protected by Secure Enclave and it never leaves your device.
"""
                )
                .foregroundColor(step2 ? .secondary : .primary)

                if !step2 {
                    Button("Set Up Backup Password") {
                        withAnimation {
                            step2 = true
                        }
                    }
                }
            }

            if step2 {
                Text(
"""
In addition to the backup password, a secret is stored on your iCloud \
Keychain that is then required to decrypt your backups. \
This additional secret protects your keys in case your backup password is compromised, \
but it's not possible to decrypt your backups with this secret alone.
"""
                )
                .foregroundColor(step3 ? .secondary : .primary)

                if !step3 {
                    Button("Enable iCloud Keychain") {
                        withAnimation {
                            step3 = true
                        }
                    }
                }
            }

            if step3 {

                VStack {
                    Text(
    """
    Make sure that iCloud Keychain sync is \
    enabled in your device settings, **otherwise you won't be able to restore the backup on a \
    new device.**
    """
                    )
                    .foregroundColor(step4 ? .secondary : .primary)

                    Image(icloudSyncScreenshot)
                        .resizable()
                        .scaledToFit()
                        .opacity(step4 ? 0.5 : 1)
                }

                if !step4 {
                    Button("I have enabled iCloud Keychain") {
                        withAnimation {
                            step4 = true
                        }
                    }
                }
            }

            if step4 {
                Text(
    """
    Make sure to write down the backup password on paper or save it in a password manager. \
    **You won't be able to recover from iCloud Storage without the backup password.**
    """
                )
                .foregroundColor(step5 ? .secondary : .primary)

                if !step5 {
                    AsyncButton(action: {
                        let success = await model.enableBackup()
                        withAnimation {
                            step5 = success
                        }
                    }, label: {
                        Text("Generate Backup Password")
                    })
                }
            }

            if step5 {
                BackupSettingsInner()
            }
        }
    }
}

struct BackupSettingsInner: View {
    @EnvironmentObject private var model: GlobalModel

    @State var showPassword: Bool = false
    @State var password: String?

    func hidePassword() {
        self.password = nil
        self.showPassword = false
    }

    var body: some View {
        Section {
            AsyncButton(action: {
                let pwd = await model.displayBackupPassword()
                UIPasteboard.general.string = pwd
            }, label: {
                Text("Copy Backup Password")
            })
            if !showPassword {
                AsyncButton(action: {
                    password = await model.displayBackupPassword()
                    showPassword = true
                }, label: {
                    Text("Reveal Backup Password")
                })
            } else {
                Button(action: {
                    hidePassword()
                }, label: {
                    Text("Hide Backup Password")
                })

                Text(password ?? "Error")
                    .onInactive {
                        hidePassword()
                    }
            }
        } header: {
            Text("Backup Password")
        }
    }
}

#if DEBUG
struct BackupSettings_Previews: PreviewProvider {
    static var previews: some View {
        Group {
            BackupSettings(backupEnabledToggle: true)
                .environmentObject(GlobalModel.buildForPreview())
            BackupSettings(backupEnabledToggle: true)
                .environmentObject(GlobalModel.buildForPreview())
                .preferredColorScheme(.dark)

            BackupSettings(backupEnabledToggle: false)
                .environmentObject(GlobalModel.buildForPreview())
            BackupSettings(backupEnabledToggle: false)
                .environmentObject(GlobalModel.buildForPreview())
                .preferredColorScheme(.dark)
        }
    }
}
#endif
