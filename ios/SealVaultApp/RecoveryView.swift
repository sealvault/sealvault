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
                    Text("Searching for backups in iCloud Storage")
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

    func setErrorBanner(title: String, detail: String = "") {
        DispatchQueue.main.async {
            self.banner = BannerData(title: title, detail: detail, type: .error)
        }
    }

    func setProcessing(_ value: Bool) {
        DispatchQueue.main.async {
            self.processing = value
        }
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
                DispatchQueue.global(qos: .userInitiated).async {
                    self.setProcessing(true)
                    var success = false
                    do {
                        try coreRestoreBackup(
                            coreArgs: GlobalModel.coreArgs(),
                            backupStorage: CoreBackupStorage(),
                            backupFileName: restoreData.backupFileName,
                            password: backupPassword
                        )
                        success = true
                    } catch CoreBackupError.FailedToFetchBackup(message: _) {
                        self.setErrorBanner(title: "Failed to download backup", detail: "Please try again")
                    } catch CoreBackupError.InvalidPassword(message: _) {
                        self.setErrorBanner(title: "Invalid backup password", detail: "Please try again")
                    } catch CoreBackupError.KdfSecretNotAvailable(message: _) {
                        self.setErrorBanner(
                            title: "iCloud Keychain not synced",
                            detail: """
Please make sure the you have iCloud Keychain sync enabled and try again a few minutes later.
""")
                    } catch {
                        self.setErrorBanner(
                            title: "Unexpected error restoring the backup",
                            detail: "Please restart the application and try again."
                        )
                        print("Error restoring backup: \(error)")
                    }
                    self.setProcessing(false)

                    if success {
                        DispatchQueue.main.async {
                            isDone = true
                        }
                    }
                }
            }, onReject: {
                confirmationPresented = true
            }, approveDisabled: $processing, rejectDisabled: $processing)
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
            let restoreData = RestoreModel(backupDate: Date.now, backupDeviceName: "Alice's iPhone", backupFileName: "")
            Group {
                RecoveryViewInner(isDone: $isDone, restoreData: restoreData)
                RecoveryViewInner(isDone: $isDone, restoreData: restoreData, processing: true)
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
