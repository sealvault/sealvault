// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct IconView: View {
    let image: Image
    @ScaledMetric var iconSize: CGFloat

    var body: some View {
        image
            .resizable()
            .aspectRatio(contentMode: .fill)
            .frame(width: iconSize, height: iconSize)
            .cornerRadius(iconSize)
            .background(
                Ellipse()
                    .frame(width: iconSize, height: iconSize)
                    .foregroundColor(Color(UIColor.secondarySystemBackground))
            )
    }
}
