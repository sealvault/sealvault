// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct AddProfile: View {
    @EnvironmentObject private var model: GlobalModel
    @EnvironmentObject private var bannerModel: BannerModel

    @Environment(\.dismiss) var dismiss

    @State var profileName: String = ""
    @State var image: Image?
    @State var imageName: String?
    @State var approveDisabled: Bool = true

    @ScaledMetric var imageSize: CGFloat = 120
    @ScaledMetric var vStackSpacing: CGFloat = 20

    private let cornerRadius: Double = 10

    var body: some View {
        let clipShape = RoundedRectangle(cornerRadius: cornerRadius, style: .continuous)

        VStack(spacing: vStackSpacing) {
            SheetTitle(title: "Create Profile")

            Spacer()

            if let image = image {
                image
                    .resizable()
                    .aspectRatio(contentMode: .fill)
                    .frame(maxWidth: imageSize, maxHeight: imageSize)
                    .clipShape(clipShape)
                    .overlay(clipShape.strokeBorder(.quaternary, lineWidth: 0.5))
            } else {
                ProgressView()
            }

            Form {
                TextField("Enter profile name", text: $profileName)
                    .accessibilityLabel("Enter Profile Name")
                    .disableAutocorrection(true)
            }
            .scrollDisabled(true)

            DialogButtons(onApprove: {
                let profileName = self.profileName
                if let imageName = self.imageName {
                    Task {
                        let maybeErrorBanner = await model.createProfile(
                            name: profileName, bundledProfilePic: imageName
                        )
                        DispatchQueue.main.async {
                            if let bannerData = maybeErrorBanner {
                                self.bannerModel.bannerData = bannerData
                            }
                            dismiss()
                        }
                    }
                }
            }, onReject: {
                dismiss()
            }, approveDisabled: $approveDisabled)
        }
        .background(Color(UIColor.systemGray6))
        .onChange(of: profileName) { newValue in
            if approveDisabled && !newValue.isEmpty && image != nil {
                approveDisabled = false
            } else if newValue.isEmpty {
                approveDisabled = true
            }
        }
        .onAppear {
            Task {
                if let name = await model.randomBundledProfilePicture() {
                    if let picture = await model.fetchBundledProfilePicture(pictureName: name) {
                        let image = Profile.convertPicture(picture)
                        DispatchQueue.main.async {
                            self.imageName = name
                            self.image = Image(uiImage: image)
                        }
                    }
                }
            }
        }
    }
}

#if DEBUG
struct AddProfile_Previews: PreviewProvider {
    static var previews: some View {
        AddProfile()
            .environmentObject(GlobalModel.buildForPreview())
            .preferredColorScheme(.dark)
    }
}
#endif
