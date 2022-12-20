// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct ProfileListView: View {
    @EnvironmentObject private var model: GlobalModel
    @State var isSettingsPresented: Bool = false

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
                Button(action: {
                    isSettingsPresented = true
                }, label: {
                    Image(systemName: "gear")
                })
            }
            .task {
                await self.model.refreshProfiles()
            }
            .sheet(isPresented: $isSettingsPresented, content: {
                Settings()
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
