// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation

class CoreUICallback: CoreUiCallbackI {
    let model: CallbackModel

    required init(_ model: CallbackModel) {
        self.model = model
    }

    func dappAllotmentTransferResult(result: DappAllotmentTransferResult) {
        DispatchQueue.main.async {
            self.model.dappAllotmentResult = result
        }
    }

    func signedMessageForDapp(result: DappSignatureResult) {
        DispatchQueue.main.async {
            self.model.dappSignatureResult = result
        }
    }

    func sentTransactionForDapp(result: DappTransactionSent) {
        DispatchQueue.main.async {
            self.model.dappTransactionSent = result
        }
    }

    func dappTransactionResult(result: DappTransactionResult) {
        DispatchQueue.main.async {
            self.model.dappTransactionResult = result
        }
    }
}
