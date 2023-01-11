// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct ProfileName: View {
    @EnvironmentObject var model: GlobalModel
    @ObservedObject var profile: Profile

    var body: some View {
        HStack(spacing: 5) {
            Text(profile.displayName)
            if model.activeProfileId == profile.id {
                Image(systemName: "checkmark.circle")
                    .foregroundColor(.green)
            }
        }.font(.headline)
    }
}
