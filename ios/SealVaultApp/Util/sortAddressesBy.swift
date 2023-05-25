// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import Foundation

func sortAddressesBy(_ first: Address, _ second: Address) -> Bool {
    if first.chain.isTestNet == second.chain.isTestNet {
        return first.chain.displayName < second.chain.displayName
    } else {
        return !first.chain.isTestNet
    }
}
