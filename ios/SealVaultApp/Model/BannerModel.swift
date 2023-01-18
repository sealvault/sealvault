// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

class BannerModel: ObservableObject {
    @Published var bannerData: BannerData?
}

struct BannerData: Equatable {
    var title: String
    var detail: String
    var type: BannerType
    var durationSeconds: Double = Config.defaultBannerDurationSeconds
}

enum BannerType {
    case info
    case warning
    case success
    case error

    var tintColor: Color {
        switch self {
        case .info:
            return Color.secondary
        case .success:
            return Color.green
        case .warning:
            return Color.yellow
        case .error:
            return Color.red
        }
    }
}

#if DEBUG
// MARK: - UI Test
extension BannerModel {
    func triggerBanners() {
        Timer.scheduledTimer(
            withTimeInterval: 1,
            repeats: true
        ) { _ in
            self.bannerData = BannerData(title: "Banner Title", detail: "", type: .info)
        }
    }
}
#endif
