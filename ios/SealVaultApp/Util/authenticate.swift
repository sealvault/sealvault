// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import LocalAuthentication

enum AuthenticationError: Error {
    case failed
    case unavailable
}

func authenticate(reason: String) async throws {
    return try await withCheckedThrowingContinuation { continuation in
        let context = LAContext()
        var error: NSError?

        if context.canEvaluatePolicy(.deviceOwnerAuthentication, error: &error) {
            context.evaluatePolicy(.deviceOwnerAuthentication, localizedReason: reason) { success, error in
                if success {
                    continuation.resume()
                } else {
                    print("Authentication error: \(String(describing: error))")
                    continuation.resume(throwing: AuthenticationError.failed)
                }
            }
        } else {
            print("Authentication unavailable")
            continuation.resume(throwing: AuthenticationError.unavailable)
        }

    }
}
