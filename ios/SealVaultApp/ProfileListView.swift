// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct ProfileListView: View {
    @EnvironmentObject private var model: GlobalModel
    @State var isSettingsPresented: Bool = false
    @State var showAddNewProfile: Bool = false

    var body: some View {
        VStack {
            ScrollViewReader { _ in
                List {
                    ForEach(model.profileList) { profile in
                        NavigationLink {
                            ProfileView(profile: profile)
                        } label: {
                            ProfileRow(profile: profile)
                                .padding(.vertical, 8)
                                .accessibilityIdentifier("\(profile.displayName) profile")
                                .contextMenu {
                                    Button(action: {
                                        UIPasteboard.general.string = profile.walletList.first?.checksumAddress
                                    }, label: {
                                        Text("Copy Wallet Address")
                                    })
                                }
                        }
                        .swipeActions(edge: .leading) {
                            Button {
                                Task {
                                    await model.setActiveProfileId(profileId: profile.id)
                                }
                            } label: {
                                Image(systemName: "checkmark.circle")
                            }
                            .tint(.green)
                        }
                        .swipeActions(edge: .trailing) {
                            Button {
                                UIPasteboard.general.string = profile.walletList.first?.checksumAddress
                            } label: {
                                Image(systemName: "doc.on.doc.fill")
                            }
                            .tint(.blue)
                        }
                    }
                }
                .accessibilityRotor("Profiles", entries: model.profileList, entryLabel: \.displayName)
                .refreshable(action: {
                    await model.refreshProfiles()
                })
            }
            .navigationTitle(Text("Profiles"))
            .toolbar {
                ToolbarItem(placement: .navigationBarLeading) {
                    Menu("Edit") {
                        Button("Add New Profile") {
                            showAddNewProfile = true
                        }
                        .accessibilityLabel(Text("Add New Profile"))
                        .disabled(model.profileList.count >= Config.maxProfiles)
                    }
                    .accessibilityLabel(Text("Edit Profiles"))
                }
                ToolbarItem(placement: .navigationBarTrailing) {
                    Button(action: {
                        isSettingsPresented = true
                    }, label: {
                        Image(systemName: "gear")
                    })
                    .overlay(
                        !model.backupEnabled ?
                            Circle()
                                .fill(.red)
                                .scaleEffect(0.33)
                                .offset(x: 11.5, y: -11.5)
                                .accessibilityLabel(Text("Backups are disabled warning"))
                        : nil
                    )
                }
            }
            .task {
                await self.model.refreshProfiles()
            }
            .sheet(isPresented: $showAddNewProfile, content: {
                AddProfile()
                    .presentationDetents([.medium])
                    .background(.ultraThinMaterial)
            })
            .sheet(isPresented: $isSettingsPresented, content: {
                NavigationView {
                    GlobalSettings()
                }
            })
        }
    }
}

#if DEBUG
struct ProfileListView_Previews: PreviewProvider {
    static var previews: some View {
        Group {
            ProfileListView().environmentObject(GlobalModel.buildForPreview())
        }
    }
}
#endif
