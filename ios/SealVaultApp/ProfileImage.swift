// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct ProfileImageRectangle: View {
    @ObservedObject var profile: Profile
    @ScaledMetric var size: CGFloat = 60

    private let cornerRadius: Double = 10

    var body: some View {
        let clipShape = RoundedRectangle(cornerRadius: cornerRadius, style: .continuous)
        profile.image
            .resizable()
            .aspectRatio(contentMode: .fill)
            .frame(maxWidth: size, maxHeight: size)
            .clipShape(clipShape)
            .overlay(clipShape.strokeBorder(.quaternary, lineWidth: 0.5))
            .accessibility(label: Text("\(profile.displayName) profile"))
    }
}

struct ProfileImageCircle: View {
    var profile: Profile
    @ScaledMetric var size: CGFloat = 30

    var body: some View {
        profile.image
            .resizable()
            .aspectRatio(contentMode: .fit)
            .frame(maxWidth: size, maxHeight: size)
            .clipShape(Circle())
            .accessibility(label: Text("\(profile.displayName) profile"))
    }
}
