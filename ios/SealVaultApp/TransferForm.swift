// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct TransferForm: View {
    @EnvironmentObject private var model: GlobalModel
    @ObservedObject var account: Account
    @ObservedObject var fromAddress: Address
    @ObservedObject var token: Token

    @State private var amount = ""
    @State private var toExternal: String = ""
    @State private var toAddress: ToAddress = ToAddress.none
    @FocusState private var amountFocused: Bool

    var toChecksumAddress: String? {
        var toChecksumAddress: String?
        if case .some(value: let toAddressId) = toAddress {
            toChecksumAddress = account.addressForAddressId(addressId: toAddressId)?.checksumAddress
        } else if toExternal != "" {
            toChecksumAddress = toExternal
        }
        return toChecksumAddress
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

            FromSection(account: account, fromAddress: fromAddress, token: token)

            ToSection(
                account: account,
                fromAddress: fromAddress,
                token: token,
                amount: $amount,
                toExternal: $toExternal,
                toAddress: $toAddress
            )

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
                        .focused($amountFocused)
                        .toolbar {
                            ToolbarItemGroup(placement: .keyboard) {
                                Spacer()
                                Button("Done") {
                                    amountFocused = false
                                }
                            }
                        }
                }
            }

            TransferButton(
                core: model.core, token: token, fromAddressId: fromAddress.id, toChecksumAddress: toChecksumAddress,
                disabled: amountFocused, amount: amount
            )
            .padding()

            Spacer()

        }
        .padding()
        .task {
            async let accounts: () = self.model.refreshAccounts()
            async let tokens: () = self.fromAddress.refreshTokens()
            // Refresh concurrently
            _ = await (accounts, tokens)
        }
    }
}

struct FromSection: View {
    @ObservedObject var account: Account
    @ObservedObject var fromAddress: Address
    @ObservedObject var token: Token

    var body: some View {
        GroupBox {
            HStack {
                if fromAddress.isWallet {
                    Text("Wallet").font(.headline)
                } else if let dapp = account.dappForAddress(address: fromAddress) {
                    DappRow(dapp: dapp)
                }
                Spacer()
                TokenLabel(token: token)
                TokenAmount(token: token)
            }
            .frame(maxWidth: .infinity)
            .padding(.top)
        } label: {
            HStack {
                Text("From")
                Spacer()
                AddressMenu(address: fromAddress)
            }
            .frame(maxWidth: .infinity)
        }
    }
}
enum ToAddress: Hashable {
    case none
    // Holds address id. Can't put address in there, bc compiler can't figure out that it
    // remains part of the Main Actor.
    case some(String)
}

struct ToSection: View {

    @ObservedObject var account: Account
    @ObservedObject var fromAddress: Address
    @ObservedObject var token: Token

    @Binding var amount: String
    @Binding var toExternal: String
    @Binding var toAddress: ToAddress
    @State var toAddressType: ToAddressType = .dapp

    enum ToAddressType {
        case wallet
        case dapp
        case external
    }

    private func setTo(_ toAddressType: ToAddressType) {
        self.toAddressType = toAddressType
        toExternal = ""
        toAddress = ToAddress.none
    }

    private func canTransferTo(_ toAddress: Address) -> Bool {
        // TODO: use protocol + chain id and move to address
        return toAddress.chainDisplayName == fromAddress.chainDisplayName && fromAddress.id != toAddress.id
    }

    var body: some View {
        GroupBox("To") {
            VStack {
                switch toAddressType {
                case .wallet:
                    Picker("Wallet", selection: $toAddress) {
                        Text("none").tag(ToAddress.none)
                        ForEach(account.walletList) { wallet in
                            if canTransferTo(wallet) {
                                Text("\(wallet.chainDisplayName) \(wallet.addressDisplay)")
                                    .tag(ToAddress.some(wallet.id))
                            }
                        }
                    }
                case .dapp:
                    Picker("Dapp", selection: $toAddress) {
                        Text("none").tag(ToAddress.none)
                        ForEach(account.dappList) { dapp in
                            ForEach(dapp.addressList) { dappAddress in
                                if canTransferTo(dappAddress) {
                                    Text("\(dapp.humanIdentifier)")
                                        .tag(ToAddress.some(dappAddress.id))
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
    }
}

struct TransferButton: View {
    var core: AppCoreProtocol
    var token: Token
    var fromAddressId: String
    var toChecksumAddress: String?
    var disabled: Bool
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
            .disabled(disabled || toChecksumAddress == nil)
            .padding()
            .background(Color.accentColor)
            .border(Color.accentColor)
            .foregroundColor(Color.white)
            .cornerRadius(8)
        }
    }
}

#if DEBUG
struct TransferView_Previews: PreviewProvider {
    static var previews: some View {
        let model = GlobalModel.buildForPreview()
        let account = model.activeAccount
        let walletAddress = account.walletList[0]
        let walletToken = Token.matic(walletAddress.checksumAddress)
        let dapp = account.dappList[0]
        let dappAddress = dapp.addressList[0]
        let dappToken = Token.dai(dapp.addressList.first!.checksumAddress)
        return Group {
            PreviewWrapper(model: model, account: account, fromAddress: dappAddress, token: dappToken)
            PreviewWrapper(model: model, account: account, fromAddress: walletAddress, token: walletToken)
        }
    }

    struct PreviewWrapper: View {
        var model: GlobalModel
        @State var account: Account
        @State var fromAddress: Address
        @State var token: Token

        var body: some View {
            TransferForm(account: account, fromAddress: fromAddress, token: token).environmentObject(model)
        }
    }
}
#endif
