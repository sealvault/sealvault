// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct TokenView: View {
    @ObservedObject var profile: Profile
    @ObservedObject var address: Address
    var paddingTop: CGFloat

    var body: some View {
        Section {
            NavigationLink {
                TransferForm(state: TransferState(profile: profile, token: address.nativeToken, fromAddress: address))
                    .navigationBarTitleDisplayMode(.inline)
            } label: {
                NativeTokenRow(address: address)
            }
            ForEach(address.fungibleTokenList) { token in
                NavigationLink {
                    TransferForm(state: TransferState(profile: profile, token: token, fromAddress: address))
                        .navigationBarTitleDisplayMode(.inline)
                } label: {
                    TokenRow(token: token)
                }
            }
        } header: {
            HStack {
                Text(address.chainDisplayName)
                if address.selectedForDapp {
                    Image(systemName: "checkmark.circle")
                }
            }
            .padding(.top, paddingTop)
            .scaledToFit()
        }
        .headerProminence(.increased)
    }
}
