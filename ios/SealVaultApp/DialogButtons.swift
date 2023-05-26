// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct DialogButtons: View {
    @State var approveLabel: String = "OK"
    @State var rejectLabel: String = "Cancel"
    @Binding var approveDisabled: Bool
    @Binding var rejectDisabled: Bool
    @Binding var loading: Bool

    var onApprove: () -> Void
    var onReject: () -> Void

    init(onApprove: @escaping () -> Void, onReject: @escaping () -> Void,
         approveDisabled: Binding<Bool>? = nil, rejectDisabled: Binding<Bool>? = nil,
         loading: Binding<Bool>? = nil) {
        self._approveDisabled = approveDisabled ?? Binding.constant(false)
        self._rejectDisabled = rejectDisabled ?? Binding.constant(false)
        self._loading = loading ?? Binding.constant(false)
        self.onApprove = onApprove
        self.onReject = onReject
    }

    var body: some View {
        HStack(spacing: 0) {
            Button(action: {
                onReject()
            }, label: {
                Text(rejectLabel)
                    .frame(maxWidth: .infinity)
                    .foregroundColor(.secondary)
            })
            .disabled(rejectDisabled)
            .accessibilityLabel(Text("Reject"))
            .buttonStyle(.borderless)
            .controlSize(.large)

            Button(action: {
                onApprove()
            }, label: {
                if loading {
                    ProgressView()
                        .frame(maxWidth: .infinity)
                } else {
                    Text(approveLabel)
                        .frame(maxWidth: .infinity)
                }
            })
            .disabled(approveDisabled)
            .accessibilityLabel(Text("Approve"))
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
