// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct DialogButtons: View {
    var onApprove: () -> Void
    var onReject: () -> Void

    var body: some View {
        HStack(spacing: 0) {
            Button(action: {
                onReject()
            }, label: {
                Text("Cancel").frame(maxWidth: .infinity).foregroundColor(.secondary)
            })
            .accessibilityLabel("reject")
            .buttonStyle(.borderless)
            .controlSize(.large)

            Button(action: {
                onApprove()
            }, label: {
                Text("OK").frame(maxWidth: .infinity)
            })
            .accessibilityLabel("approve")
            .buttonStyle(.borderless)
            .controlSize(.large)
        }
    }
}

struct DialogButtons_Previews: PreviewProvider {
    static var previews: some View {
        DialogButtons(onApprove: {}, onReject: {})
    }
}
