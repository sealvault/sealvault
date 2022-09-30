// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct TransferForm: View {
    enum ToAddressType {
        case wallet
        case dapp
        case external
    }

    @EnvironmentObject private var model: GlobalModel
    var account: Account
    var fromAddress: Address
    @Binding var token: Token

    @State private var amount = ""
    @State private var toExternal: String = ""
    @State private var toAddress: Address?
    @State private var toAddressType: ToAddressType = .dapp

    var toChecksumAddress: String? {
        var toChecksumAddress: String?
        if let toAddr = toAddress {
            toChecksumAddress = toAddr.checksumAddress
        } else if toExternal != "" {
            toChecksumAddress = toExternal
        }
        return toChecksumAddress
    }

    private func setTo(_ toAddressType: ToAddressType) {
        self.toAddressType = toAddressType
        toExternal = ""
        toAddress = nil
    }

    var body: some View {
        VStack(spacing: 20) {
            Spacer()

            VStack(spacing: 0) {
                HStack {
                    Text("Transfer")
                    TokenLabel(token: token)
                }.font(.largeTitle)
                HStack {
                    Text("on \(fromAddress.chainDisplayName)")
                }.font(.title2)
            }

            Spacer()

            GroupBox {
                HStack {
                    if account.isWallet(address: fromAddress) {
                        Text("Wallet").font(.headline)
                    } else if let dapp = account.dappForAddress(address: fromAddress) {
                        DappRow(dapp: dapp)
                    }
                    Spacer()
                    TokenLabel(token: token)
                    TokenAmount(token: $token)
                }
                .frame(maxWidth: .infinity)
                .padding(.top)
            } label: {
                HStack {
                    Text("From")
                    Spacer()
                    AddressMenu(address: fromAddress)
                }.frame(maxWidth: .infinity)
            }
            GroupBox("To") {
                VStack {
                    switch toAddressType {
                    case .wallet:
                        Picker("Wallet", selection: $toAddress) {
                            Text("none").tag(nil as Address?)
                            ForEach(account.wallets) { wallet in
                                // TODO: use protocol + chain id and move to address
                                if wallet.chainDisplayName == fromAddress.chainDisplayName &&
                                    fromAddress.id != wallet.id {
                                    Text("\(wallet.chainDisplayName) \(wallet.addressDisplay)").tag(wallet as Address?)
                                }
                            }
                        }
                    case .dapp:
                        Picker("Dapp", selection: $toAddress) {
                            Text("none").tag(nil as Dapp?)
                            ForEach(account.dapps) { dapp in
                                ForEach(dapp.addresses) { dappAddress in
                                    // TODO: use protocol + chain id and move to address
                                    if dappAddress.chainDisplayName == fromAddress.chainDisplayName &&
                                        fromAddress.id != dappAddress.id {
                                        Text("\(dapp.humanIdentifier) \(dappAddress.addressDisplay)")
                                            .tag(dappAddress as Address?)
                                    }
                                }
                            }
                        }
                    case .external:
                        TextField("Address", text: $toExternal)
                            .textFieldStyle(.roundedBorder)
                            .padding(.horizontal)
                            .keyboardType(.alphabet)
                    }
                    Picker("to", selection: $toAddressType) {
                        Button(action: {
                            setTo(ToAddressType.wallet)
                        }, label: {
                            Text("Wallet")
                        }).tag(ToAddressType.wallet)
                        Button(action: {
                            setTo(ToAddressType.dapp)
                        }, label: {
                            Text("Dapp")
                        }).tag(ToAddressType.dapp)
                        Button(action: {
                            setTo(ToAddressType.external)
                        }, label: {
                            Text("External")
                        }).tag(ToAddressType.external)
                    }.pickerStyle(.segmented)
                }
            }
            GroupBox("Amount") {
                HStack {
                    Label {
                        Text(token.symbol)
                    }
                    icon: {
                        IconView(image: token.image, iconSize: 24)
                            .accessibility(label: Text("Token icon"))
                    }
                    TextField("amount", text: $amount)
                        .multilineTextAlignment(.trailing)
                        .textFieldStyle(.roundedBorder)
                        .padding(.horizontal)
                        .keyboardType(.decimalPad)
                }
            }

            Spacer()

            TransferButton(
                core: model.core, token: token, fromAddressId: fromAddress.id, toChecksumAddress: toChecksumAddress,
                amount: amount
            ).padding()

        }.padding()
    }
}

struct TransferButton: View {
    var core: AppCoreProtocol
    var token: Token
    var fromAddressId: String
    var toChecksumAddress: String?
    var amount: String
    @State private var txExplorerUrl: URL?

    var body: some View {
        if let url = txExplorerUrl {
            Button(action: {
                UIApplication.shared.open(url)
            }, label: {
                Text("View Transaction")
                    .frame(maxWidth: .infinity)
            })
            .padding()
            .background(Color.secondary)
            .border(Color.secondary)
            .foregroundColor(Color.white)
            .cornerRadius(50)
        } else {
            // TODO: turn this into a swipe button
            Button(action: {
                do {
                    if let toAddress = toChecksumAddress {
                        var txHash: String
                        if token.nativeToken {
                            txHash = try core.ethTransferNativeToken(
                                fromAddressId: fromAddressId, toChecksumAddress: toAddress, amount: amount
                            )
                        } else {
                            txHash = try core.ethTransferFungibleToken(
                                fromAddressId: fromAddressId, toChecksumAddress: toAddress, amount: amount,
                                tokenId: token.id
                            )
                        }
                        let rawUrl = try core.ethTransactionBlockExplorerUrl(
                            fromAddressId: fromAddressId, txHash: txHash
                        )
                        if let url = URL(string: rawUrl) {
                            txExplorerUrl = url
                        } else {
                            print("Invalid block explorer url: \(rawUrl)")
                        }
                    }
                } catch {
                    // TODO: handle different errors
                    print("Error: \(error)")
                }
            }, label: {
                Text("Send")
                    .frame(maxWidth: .infinity)
            })
            .disabled(toChecksumAddress == nil)
            .padding()
            .background(Color.accentColor)
            .border(Color.accentColor)
            .foregroundColor(Color.white)
            .cornerRadius(50)
        }
    }
}

struct TransferView_Previews: PreviewProvider {
    static var previews: some View {
        let model = GlobalModel.buildForPreview()
        let account = model.activeAccount
        let walletAddress = account.wallets[0]
        let walletToken = Token.matic()
        let dapp = account.dapps[0]
        let dappAddress = dapp.addresses[0]
        let dappToken = Token.dai()
        return Group {
            PreviewWrapper(model: model, account: account, fromAddress: dappAddress, token: dappToken)
            PreviewWrapper(model: model, account: account, fromAddress: walletAddress, token: walletToken)
        }
    }

    struct PreviewWrapper: View {
        var model: GlobalModel
        var account: Account
        var fromAddress: Address
        @State var token: Token

        var body: some View {
            TransferForm(account: account, fromAddress: fromAddress, token: $token).environmentObject(model)
        }
    }
}
