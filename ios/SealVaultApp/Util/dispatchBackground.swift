// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation

func dispatchBackground<T>(_ qos: DispatchQoS.QoSClass, blockingCall: @escaping () -> T ) async -> T {

    func dispatch(completion: @escaping (T) -> Void) {
        DispatchQueue.global(qos: qos).async {
            let result: T = blockingCall()
            completion(result)
        }
    }

    // Suspend the current task until dispatch calls the completion callback
    return await withCheckedContinuation { continuation in
        dispatch { result in
            continuation.resume(returning: result)
        }
    }
}
