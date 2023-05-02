// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct SheetTitle: View {
    @State var title: String
    @ScaledMetric var paddingTop: CGFloat = 40

    var body: some View {
        Text(title)
            .font(.title)
            .padding(.top, paddingTop)
    }
}
