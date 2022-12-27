// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

// Based on: https://stackoverflow.com/a/70497752
// Additional license: https://creativecommons.org/licenses/by-sa/4.0/
struct CustomSecureField: View {
    @Binding var password: String
    @State var placeholder: String = "Password"

    @FocusState var focused: FocusedField?
    @State var showPassword: Bool = false

    var body: some View {
        HStack {
            ZStack(alignment: .trailing) {
                TextField(placeholder, text: $password)
                    .focused($focused, equals: .unSecure)
                    .autocapitalization(.none)
                    .disableAutocorrection(true)
                // This is needed to remove suggestion bar, otherwise swapping between
                // fields will change keyboard height and be distracting to user.
                    .keyboardType(.alphabet)
                    .opacity(showPassword ? 1 : 0)
                SecureField(placeholder, text: $password)
                    .focused($focused, equals: .secure)
                    .autocapitalization(.none)
                    .disableAutocorrection(true)
                    .opacity(showPassword ? 0 : 1)
                Button(action: {
                    showPassword.toggle()
                    focused = focused == .secure ? .unSecure : .secure
                }, label: {
                    Image(systemName: self.showPassword ? "eye.slash.fill" : "eye.fill")
                        .padding()
                })
                .disabled(password.isEmpty)
            }
            .keyboardType(.asciiCapable)
        }
        .onInactive {
            showPassword = false
        }
    }
    // Using the enum makes the code clear as to what field is focused.
    enum FocusedField {
        case secure, unSecure
    }
}
