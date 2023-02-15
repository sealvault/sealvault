// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation

class CallbackModel: ObservableObject {
    @Published var tokenTransferResult: TokenTransferResult?
    @Published var tokenTransferSent: TokenTransferResult?
    @Published var dappAllotmentResult: DappAllotmentTransferResult?
    @Published var dappSignatureResult: DappSignatureResult?
    @Published var dappTransactionApproved: DappTransactionApproved?
    @Published var dappTransactionResult: DappTransactionResult?
}
