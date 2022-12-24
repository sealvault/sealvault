// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct RecoveryView: View {

    @Binding var isDone: Bool
    @State var restoreData: RestoreModel
    @State var backupPassword: String = ""
    @State var confirmationPresented: Bool = false
    @State var displayPassword: Bool = false

    var backupDate: String {
        restoreData.backupDate.formatted()
    }

    var body: some View {
        VStack(alignment: .center, spacing: 40) {

            Text("Restore Backup")
                .font(.largeTitle)
                .bold()

            VStack(alignment: .leading, spacing: 20) {
                Text("The last backup was created at \(backupDate) on \(restoreData.backupDeviceName).")

                Text("Please enter your backup password to continue.")

            }

            HStack {
                Spacer()
                CustomSecureField(password: $backupPassword, placeholder: "XXXXX-XXXXX-XXXXX-XXXXX")
                    .multilineTextAlignment(.center)
                Spacer()

            }
            .frame(maxWidth: .infinity)

            Spacer()
            DialogButtons(approveDisabled: backupPassword.isEmpty, onApprove: {
                print("approved")
            }, onReject: {
                print("cancelled")
            })
        }
        .confirmationDialog("Are you store you don't want to restore from backup", isPresented: $confirmationPresented,
            actions: {
                Button("Yes", role: .destructive, action: {
                    isDone = true
                })
                Button("Go back", role: .cancel, action: {
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
                RecoveryView(isDone: $isDone, restoreData: restoreData)
                RecoveryView(isDone: $isDone, restoreData: restoreData)
                    .preferredColorScheme(.dark)

            }
        }
    }

    static var previews: some View {
        RecoveryViewPreviewContainer()
    }
}
