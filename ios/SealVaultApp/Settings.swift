// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation
import SwiftUI

struct Settings: View {
    @EnvironmentObject private var viewModel: GlobalModel
    @State var backupsEnabled: Bool = true
    @State var showPassword: Bool = false
    @State var showConfirmation: Bool = false
    @State var didConfirmPassword: Bool = false
    @State private var password: String = "8FD93-EYWZR-GB7HX-QAVNS"

    var body: some View {
        let isBackupOn = Binding<Bool>(
            get: { self.backupsEnabled },
            set: {
                self.backupsEnabled = $0
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
                            Image(systemName: "icloud").foregroundColor(Color.secondary)
                        }
                    }
                    .alert(
                        "Save backup password",
                         isPresented: $showConfirmation
                    ) {
                        Button("OK") {
                            backupsEnabled = true
                        }
                    } message: {
                        Text("""
Make sure to write down the backup password on paper or save it in a password manager.
You won't be able to recover from iCloud Storage without the backup password.
""")
                    }

                    let rowInsets = EdgeInsets(top: 0, leading: 60, bottom: 0, trailing: 0)

                    if backupsEnabled {
                        Button(action: {
                            UIPasteboard.general.string = password
                        }, label: {
                            Text("Copy Backup Password")
                        })
                        .listRowInsets(rowInsets)

                        if !showPassword {
                            Button(action: {
                                showPassword = true
                            }, label: {
                                Text("Reveal Backup Password")
                            })
                            .listRowInsets(rowInsets)

                        } else {
                            Button(action: {
                                showPassword = false
                            }, label: {
                                Text("Hid Backup Password")
                            })
                            .listRowInsets(rowInsets)

                            Text(password)
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
