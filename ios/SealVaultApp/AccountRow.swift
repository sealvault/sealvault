// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct AccountRow: View {
    @Binding var account: Account

    private let cornerRadius: Double = 10
    private let maxDapps = 3

    var body: some View {
        HStack(alignment: .top) {
            AccountImageRectangle(account: account)

            VStack(alignment: .leading) {
                Text(account.displayName)
                    .font(.headline)

                Text(account.topDapps)
                    .lineLimit(2)
                    .foregroundStyle(.secondary)
            }

            Spacer(minLength: 0)
        }
        .font(.subheadline)
        .accessibilityElement(children: .combine)
    }
}

struct AccountRow_Previews: PreviewProvider {
    static var previews: some View {
        let model = GlobalModel.buildForPreview()
        return PreviewWrapper(account: model.activeAccount)
    }

    struct PreviewWrapper: View {
        @State var account: Account
        var body: some View {
            AccountRow(account: $account)
        }
    }

}
