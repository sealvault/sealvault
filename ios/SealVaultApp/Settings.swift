// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation
import SwiftUI

struct Settings: View {
    @EnvironmentObject private var model: GlobalModel
    @State var settingUpBackup: Bool = false
    @State var showPassword: Bool = false
    @State var showConfirmation: Bool = false
    @State var didConfirmPassword: Bool = false
    @State var password: String?

    var body: some View {
        let isBackupOn = Binding<Bool>(
            get: { return settingUpBackup || model.backupEnabled },
            set: {
                self.showConfirmation = $0
            }
        )

        VStack {
            List {
                Section {
                    Toggle(isOn: isBackupOn) {
                        Label {
                            Text("iCloud Storage Backup")
                        } icon: {
                            if settingUpBackup {
                                ProgressView()
                            } else {
                                Image(systemName: "icloud").foregroundColor(Color.secondary)
                            }
                        }
                    }
                    .alert(
                        "Save backup password",
                         isPresented: $showConfirmation
                    ) {
                        Button("OK") {
                            Task {
                                settingUpBackup = true
                                await model.enableBackup()
                                settingUpBackup = false
                            }
                        }
                    } message: {
                        Text("""
Make sure to write down the backup password on paper or save it in a password manager.
You won't be able to recover from iCloud Storage without the backup password.
""")
                    }

                    let rowInsets = EdgeInsets(top: 0, leading: 60, bottom: 0, trailing: 0)

                    if model.backupEnabled && !settingUpBackup {
                        AsyncButton(action: {
                            let pwd = await model.displayBackupPassword()
                            UIPasteboard.general.string = pwd
                        }, label: {
                            Text("Copy Backup Password")
                        })
                        .listRowInsets(rowInsets)

                        if !showPassword {
                            AsyncButton(action: {
                                password = await model.displayBackupPassword()
                                showPassword = true
                            }, label: {
                                Text("Reveal Backup Password")
                            })
                            .listRowInsets(rowInsets)

                        } else {
                            Button(action: {
                                password = nil
                                showPassword = false
                            }, label: {
                                Text("Hid Backup Password")
                            })
                            .listRowInsets(rowInsets)

                            Text(password ?? "Error")
                            .listRowInsets(rowInsets)

                        }
                    }
                } header: {
                    Text("Device Backup")
                }
            }
        }
        .navigationTitle("Settings")
    }
}

#if DEBUG
struct Settings_Previews: PreviewProvider {
    static var previews: some View {
        Group {
            Settings()
                .environmentObject(GlobalModel.buildForPreview())
            Settings()
                .environmentObject(GlobalModel.buildForPreview())
                .preferredColorScheme(.dark)
        }
    }
}
#endif
