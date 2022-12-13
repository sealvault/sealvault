// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct WalletRow: View {
    @ObservedObject var profile: Profile

    var body: some View {
        HStack {
            VStack(alignment: .leading) {
                Text("Profile Wallet")
                    .font(.headline)

                Text(profile.walletChains)
                    .lineLimit(2)
                    .foregroundStyle(.secondary)
                    .font(.subheadline)
            }
        }
    }
}

#if DEBUG
struct WalletRow_Previews: PreviewProvider {
    static var previews: some View {
        let model = GlobalModel.buildForPreview()
        let profile = model.activeProfile!
        return WalletRow(profile: profile)
    }
}
#endif
