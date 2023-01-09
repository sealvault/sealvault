// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation
import SwiftUI

struct BackupSettings: View {
    @EnvironmentObject private var model: GlobalModel
    @Environment(\.presentationMode) var presentationMode: Binding<PresentationMode>

    @State var backupEnabledToggle: Bool = false
    @State var isDeveloper: Bool = false
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
                        LastBackupRow()
                    } header: {
                        Text("Device Backup")
                    } footer: {
                        Text("Backups are created when you exit the app.")
                    }

                    BackupPasswordDisplay()

                    Section {
                        Toggle(isOn: $isDeveloper) {
                            Text("Developer Enabled")
                        }
                        if isDeveloper {
                            NavigationLink {
                                BackupDebug(debugInfo: [])
                            } label: {
                                Text("Debug")
                            }
                        }
                    } header: {
                        Text("Developer Mode")
                    }
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
    @Environment(\.colorScheme) private var colorScheme

    @State var step: Int = 0
    @State var showPopUp: Bool = false

    var progress: Double {
        (Double(step) / BackupSettingsOnboardingInner.maxStep)
    }
    var icloudSyncScreenshot: String {
        colorScheme == .dark ? "icloud-sync-setting-screenshot-dark" : "icloud-sync-setting-screenshot-light"
    }

    var body: some View {
        ZStack(alignment: .top) {
            BackupSettingsOnboardingInner(step: $step, showPopUp: $showPopUp)
            ProgressView(value: progress)

            if showPopUp {
                ZStack {
                    Color
                        .black
                        .opacity(0.4)
                        .ignoresSafeArea()
                    VStack {
                        Text(
"""
You can enable iCloud Keychain in *Settings* -> *Apple ID* -> *iCloud* -> *Passwords and Keychain* as pictured on the \
screenshot below:
"""
                        )
                            .padding()
                        Image(icloudSyncScreenshot)
                            .resizable()
                            .scaledToFit()

                        Button(action: {
                            showPopUp = false
                        }, label: {
                            Text("Close")
                        })
                        .padding()
                    }
                    .background(Color(UIColor.systemGray5))
                    .frame(width: 350, height: 525)
                    .cornerRadius(20)
                    .shadow(radius: 20)
                    .padding()
                }
            }
        }
    }
}

struct BackupSettingsOnboardingInner: View {
    @EnvironmentObject private var model: GlobalModel

    @Binding var step: Int
    static let maxStep = 5.0

    @Binding var showPopUp: Bool

    // We can't derive from `step` bc then it'd rerender every change and screw up scrolling
    @State var step1: Bool = false
    @State var step2: Bool = false
    @State var step3: Bool = false
    @State var step4: Bool = false
    @State var step5: Bool = false

    func setStep(_ step: Int) {
        DispatchQueue.main.async {
            withAnimation {
                self.step = step

                switch step {
                case 1:
                    step1 = true
                case 2:
                    step2 = true
                case 3:
                    step3 = true
                case 4:
                    step4 = true
                case 5:
                    step5 = true
                default:
                    print("Unexpected step: \(step)")
                }
            }
        }
    }

    var body: some View {
        ScrollViewReader { proxy in
            Form {

                Text(
"""
Automatically back up your keys and profiles to your iCloud Storage so that you can \
restore them if you lose your device or get a new one.
"""
                )
                .foregroundColor(step1 ? .secondary : .primary)
                .id(0)

                if !step1 {
                    Button("Enable Backups") {
                        setStep(1)
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
                    .id(1)

                    if !step2 {
                        Button("Set Up Backup Password") {
                            setStep(2)
                        }
                    }
                }

                if step2 {
                    Text(
"""
In addition to the backup password, a secret is stored on your iCloud \
Keychain that is required to decrypt your backups. \
This additional secret protects your keys in case your backup password is stolen, \
but it's not possible to decrypt your backups with this secret alone.
"""
                    )
                    .foregroundColor(step3 ? .secondary : .primary)
                    .id(2)

                    if !step3 {
                        Button("Enable iCloud Keychain") {
                            setStep(3)
                        }
                    }
                }

                if step3 {
                    Text(
"""
Make sure that iCloud Keychain sync is \
enabled in your device settings, **otherwise you won't be able to restore the backup on a \
new device.**
"""
                    )
                    .foregroundColor(step4 ? .secondary : .primary)
                    .id(3)

                    if !step4 {
                        Button("Show Me How") {
                            showPopUp = true
                        }
                        Button("I Have Enabled iCloud Keychain") {
                            setStep(4)
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
                    .id(4)

                    if !step5 {
                        AsyncButton(action: {
                            let success = await model.enableBackup()
                            if success {
                                setStep(5)
                            }
                        }, label: {
                            Text("Generate Backup Password")
                        })
                    }
                }
                BackupPasswordDisplay()
                    .id(5)
                    .disabled(!step5)

            }
            .onChange(of: step) { _ in
                withAnimation {
                    proxy.scrollTo(5)
                }
            }
        }
    }
}

struct BackupPasswordDisplay: View {
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
                do {
                    try await authenticate(reason: "Copy backup password")
                    let pwd = await model.displayBackupPassword()
                    UIPasteboard.general.string = pwd
                } catch {
                    print("Error copying backup password: \(error)")
                }
            }, label: {
                Text("Copy Backup Password")
            })
            if !showPassword {
                AsyncButton(action: {
                    do {
                        try await authenticate(reason: "Reveal backup password")
                        password = await model.displayBackupPassword()
                        showPassword = true
                    } catch {
                        print("Error revealing backup password: \(error)")
                    }
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

struct LastBackupRow: View {
    @EnvironmentObject private var model: GlobalModel

    @State var lastBackup: Date?

    var body: some View {
        HStack {
            Label("Last backup", systemImage: "clock")
            Spacer()
            if let lastBackup = self.lastBackup {
                Text(lastBackup.formatted())
            } else {
                ProgressView()
            }
        }
        .onAppear {
            Task {
                let lastBackup = await model.fetchLastBackup()
                DispatchQueue.main.async {
                    self.lastBackup = lastBackup
                }
            }
        }
    }
}

struct BackupDebug: View {
    @State var debugInfo: [BackupDebugInfo]

    var body: some View {
        VStack {
            List(debugInfo) { info in
                /*@START_MENU_TOKEN@*/Text(info.path)/*@END_MENU_TOKEN@*/
                    .font(.subheadline)
                ForEach(info.attributes.sorted(by: <), id: \.key) { key, value in
                    HStack {
                        Text(key)
                            .font(.caption)
                        Spacer()
                        Text(value)
                            .font(.caption2)
                    }
                    .listRowInsets(EdgeInsets(top: 0, leading: 60, bottom: 0, trailing: 0))
                }
            }
            .padding()
            .listStyle(.inset)
        }
        .onAppear {
            DispatchQueue.global(qos: .userInitiated).async {
                let debugInfo = CoreBackupStorage.debugInfo()
                DispatchQueue.main.async {
                    withAnimation {
                        self.debugInfo = debugInfo
                    }
                }
            }
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
        }
    }
}
#endif
