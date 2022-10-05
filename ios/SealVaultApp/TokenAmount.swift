// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct TokenAmount: View {
    @ObservedObject var token: Token

    var body: some View {
        if let amount = token.amount {
            if amount.count > 12 {
                let prefix = String(amount.prefix(9))
                Text("\(prefix)...")
            } else {
                Text(amount)
            }
        } else {
            ProgressView()
        }
    }
}
