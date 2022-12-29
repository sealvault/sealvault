// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct RecoveryView: View {
    @Binding var isDoneRestoring: Bool
    @ObservedObject var recoveryModel: RecoveryModel

    @State var showAlert: Bool = false

    var body: some View {
        if let restoreData = recoveryModel.restoreData {
            RecoveryViewInner(isDone: $isDoneRestoring, restoreData: restoreData)
        } else {
            VStack {
                Spacer()
                VStack {
                    Text("Downloading backups from iCloud Storage")
                        .multilineTextAlignment(.center)
                    ProgressView()
                }
                Spacer()
            }
            .onChange(of: recoveryModel.didFinish) { newValue in
                if newValue && recoveryModel.restoreData == nil {
                    showAlert = true
                }
            }
            .alert("Error", isPresented: $showAlert) {
                Button("Start app without restoring", role: .destructive) {
                    withAnimation {
                        isDoneRestoring = true
                    }
                }
                Button("Try again", role: .cancel) {
                    recoveryModel.start()
                }
            } message: {
                Text("Failed to download backups from iCloud Storage. Start app without restoring or try again?")
            }
            .padding(.horizontal, 20)
        }
    }
}

struct RecoveryViewInner: View {
    @Binding var isDone: Bool
    @ObservedObject var restoreData: RestoreModel

    @State var backupPassword: String = ""
    @State var confirmationPresented: Bool = false
    @State var displayPassword: Bool = false
    @State var processing: Bool = false
    @State var banner: BannerData?

    var backupDate: String {
        restoreData.backupDate.formatted()
    }

    var body: some View {
        VStack(alignment: .center, spacing: 40) {

            Text("Restore Backup")
                .font(.largeTitle)
                .bold()
                .padding(.top, 60)

            Spacer()

            VStack(alignment: .leading, spacing: 20) {
                Text("The last backup was created at \(backupDate) on \(restoreData.backupDeviceName).")

                Text("Please enter your backup password to continue.")
            }

            HStack {
                Spacer()
                if processing {
                    ProgressView()
                } else {
                    CustomSecureField(password: $backupPassword, placeholder: "XXXXX-XXXXX-XXXXX-XXXXX")
                        .multilineTextAlignment(.center)
                }
                Spacer()

            }
            .frame(maxWidth: .infinity)

            Spacer()
            Spacer()
            DialogButtons(onApprove: {
                if backupPassword.isEmpty {
                    banner = BannerData(title: "Please enter a backup password", detail: "", type: .error)
                    return
                }
                Task {
                    processing = true
                    let success = await dispatchBackground(.userInteractive) {
                        do {
                            try coreRestoreBackup(
                                coreArgs: GlobalModel.coreArgs(),
                                fromPath: restoreData.backupFilePath,
                                password: backupPassword
                            )
                            return true
                        } catch {
                            print("Error restoring backup: \(error)")
                        }
                        return false
                    }
                    if !success {
                        banner = BannerData(
                            title: "Failed to decrypt backup",
                            detail: """
Please make sure that the backup password is correct and that you have iCloud Keychain enabled.
"""
                            , type: .error)
                    } else {
                        isDone = true
                    }
                    processing = false
                }
            }, onReject: {
                confirmationPresented = true
            })
        }
        .banner(data: $banner)
        .confirmationDialog("Are you store you don't want to restore from backup?", isPresented: $confirmationPresented,
            actions: {
                Button("Abandon backup", role: .destructive, action: {
                    isDone = true
                })
                Button("Continue restoring", role: .cancel, action: {
                    confirmationPresented = false
                })
        })
        .padding(.top, 60)
        .padding(.horizontal, 20)
    }
}

struct RecoveryView_Previews: PreviewProvider {
    struct RecoveryViewPreviewContainer: View {
        @State private var isDone = false

        var body: some View {
            let restoreData = RestoreModel(backupDate: Date.now, backupDeviceName: "Alice's iPhone", backupFilePath: "")
            Group {
                RecoveryViewInner(isDone: $isDone, restoreData: restoreData)
                RecoveryViewInner(isDone: $isDone, restoreData: restoreData)
                    .preferredColorScheme(.dark)
                RecoveryView(isDoneRestoring: $isDone, recoveryModel: RecoveryModel.buildForPreview())
                RecoveryView(isDoneRestoring: $isDone, recoveryModel: RecoveryModel.buildForPreview())
                    .preferredColorScheme(.dark)
            }
        }
    }

    static var previews: some View {
        RecoveryViewPreviewContainer()
    }
}
