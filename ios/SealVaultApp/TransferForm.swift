// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

class TransferState: ObservableObject {
    @Published var account: Account
    @Published var fromAddress: Address
    @Published var token: Token

    @Published var toExternal: String = ""
    @Published var toAddress: ToAddress = ToAddress.none

    @Published var disableButton: Bool = false
    @Published var amount: String = ""

    @Published var processing: Bool = false
    @Published var txExplorerUrl: URL?

    var buttonDisabled: Bool {
        return processing || disableButton || toChecksumAddress == nil || amount == ""
    }

    var toChecksumAddress: String? {
        var toChecksumAddress: String?
        if case .some(value: let toAddressId) = toAddress {
            toChecksumAddress = account.addressForAddressId(addressId: toAddressId)?.checksumAddress
        } else if toExternal != "" {
            toChecksumAddress = toExternal
        }
        return toChecksumAddress
    }

    required init(
        account: Account, token: Token, fromAddress: Address
    ) {
        self.account = account
        self.token = token
        self.fromAddress = fromAddress
    }
}

struct TransferForm: View {
    @EnvironmentObject var model: GlobalModel
    @ObservedObject var state: TransferState

    @FocusState private var amountFocused: Bool

    var body: some View {
        VStack(spacing: 20) {
            Spacer()

            VStack(spacing: 0) {
                HStack {
                    Text("Transfer")
                    TokenLabel(token: state.token)
                }.font(.largeTitle)
                HStack {
                    Text("on \(state.fromAddress.chainDisplayName)")
                }.font(.title2)
            }

            Spacer()

            FromSection(state: state)

            ToSection(state: state)

            GroupBox("Amount") {
                HStack {
                    Label {
                        Text(state.token.symbol)
                    }
                    icon: {
                        IconView(image: state.token.image, iconSize: 24)
                            .accessibility(label: Text("Token icon"))
                    }
                    TextField("amount", text: $state.amount)
                        .multilineTextAlignment(.trailing)
                        .textFieldStyle(.roundedBorder)
                        .padding(.horizontal)
                        .keyboardType(.decimalPad)
                        .focused($amountFocused)
                        .onChange(of: amountFocused, perform: { newValue in
                            state.disableButton = newValue
                        })
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
                core: model.core, state: state
            )
            .padding()

            Spacer()

        }
        .padding()
        .task {
            async let accounts: () = self.model.refreshAccounts()
            async let tokens: () = self.state.fromAddress.refreshTokens()
            // Refresh concurrently
            _ = await (accounts, tokens)
        }
    }
}

struct FromSection: View {
    @ObservedObject var state: TransferState

    var body: some View {
        GroupBox {
            HStack {
                if state.fromAddress.isWallet {
                    Text("Wallet")
                        .font(.headline)
                } else if let dapp = state.account.dappForAddress(address: state.fromAddress) {
                    DappRow(dapp: dapp)
                }
                Spacer()
                TokenLabel(token: state.token)
                TokenAmount(token: state.token)
            }
            .frame(maxWidth: .infinity)
            .padding(.top)
        } label: {
            HStack {
                Text("From")
                Spacer()
                AddressMenu(address: state.fromAddress)
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
    @ObservedObject var state: TransferState

    @State var toAddressType: ToAddressType = .dapp

    enum ToAddressType {
        case wallet
        case dapp
        case external
    }

    private func setTo(_ toAddressType: ToAddressType) {
        self.toAddressType = toAddressType
        state.toExternal = ""
        state.toAddress = ToAddress.none
    }

    private func canTransferTo(_ toAddress: Address) -> Bool {
        // TODO: use protocol + chain id and move to address
        return toAddress.chainDisplayName == state.fromAddress.chainDisplayName && state.fromAddress.id != toAddress.id
    }

    var body: some View {
        GroupBox("To") {
            VStack {
                switch toAddressType {
                case .wallet:
                    Picker("Wallet", selection: $state.toAddress) {
                        Text("none").tag(ToAddress.none)
                        ForEach(state.account.walletList) { wallet in
                            if canTransferTo(wallet) {
                                Text("\(wallet.chainDisplayName) \(wallet.addressDisplay)")
                                    .tag(ToAddress.some(wallet.id))
                            }
                        }
                    }
                case .dapp:
                    Picker("Dapp", selection: $state.toAddress) {
                        Text("none").tag(ToAddress.none)
                        ForEach(state.account.dappList) { dapp in
                            ForEach(dapp.addressList) { dappAddress in
                                if canTransferTo(dappAddress) {
                                    Text("\(dapp.humanIdentifier)")
                                        .tag(ToAddress.some(dappAddress.id))
                                }
                            }
                        }
                    }
                case .external:
                    TextField("Address", text: $state.toExternal)
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
    let core: AppCoreProtocol
    let cornerRadius: CGFloat = 8

    @ObservedObject var state: TransferState

    func makeTransfer() async {
        state.txExplorerUrl = await dispatchBackground(.userInteractive) {
            do {
                if let toAddress = state.toChecksumAddress {
                    var txHash: String
                    if state.token.nativeToken {
                        txHash = try core.ethTransferNativeToken(
                            fromAddressId: state.fromAddress.id, toChecksumAddress: toAddress, amount: state.amount
                        )
                    } else {
                        txHash = try core.ethTransferFungibleToken(
                            fromAddressId: state.fromAddress.id, toChecksumAddress: toAddress, amount: state.amount,
                            tokenId: state.token.id
                        )
                    }
                    let rawUrl = try core.ethTransactionBlockExplorerUrl(
                        fromAddressId: state.fromAddress.id, txHash: txHash
                    )
                    return URL(string: rawUrl)
                } else {
                    return nil
                }
            } catch {
                // TODO: handle different errors
                print("Error: \(error)")
                return nil
            }
        }
        // TODO we should update the balance in the transfer view after the transfer, but calling this here resets
        // the view and makes the success button disappear.
//        await state.fromAddress.refreshTokens()
    }

    var body: some View {

        if let url = state.txExplorerUrl {
            Button(action: {
                UIApplication.shared.open(url)
            }, label: {
                Text("View Transaction")
                    .frame(maxWidth: .infinity)
            })
            .padding()
            .background(Color.green)
            .foregroundColor(Color.white)
            .cornerRadius(cornerRadius)
        } else {
            Button(action: {
                if state.processing {
                    return
                }
                Task {
                    state.processing = true
                    await makeTransfer()
                    state.processing = false
                }
            }, label: {
                if state.processing {
                        HStack {
                            ProgressView()
                                .progressViewStyle(CircularProgressViewStyle())
                            Text("Sending")
                        }
                            .frame(maxWidth: .infinity)
                    } else {
                        Text("Send")
                            .frame(maxWidth: .infinity)
                    }
            })
            .disabled(state.buttonDisabled)
            .padding()
            .background(state.buttonDisabled ? Color.secondary : Color.accentColor)
            .foregroundColor(Color.white)
            .cornerRadius(cornerRadius)
        }
    }
}

#if DEBUG
struct TransferView_Previews: PreviewProvider {
    static var previews: some View {
        let model = GlobalModel.buildForPreview()
        let account = model.activeAccount!
        let walletAddress = account.walletList[0]
        let walletToken = Token.matic(walletAddress.checksumAddress)
        let dapp = account.dappList[0]
        let dappAddress = dapp.addressList[0]
        let dappToken = Token.dai(dapp.addressList.first!.checksumAddress)
        return Group {
            PreviewWrapper(
                model: model,
                state: TransferState(account: account, token: dappToken, fromAddress: dappAddress)
            )
            PreviewWrapper(
                model: model,
                state: TransferState(account: account, token: walletToken, fromAddress: walletAddress)
            )
        }
    }

    struct PreviewWrapper: View {
        var model: GlobalModel
        var state: TransferState

        var body: some View {
            // Recreated on purpose every time the view is showed to reset the UI so that the user doesn't mistakenly
            // send the wrong amount after continuing.

            TransferForm(state: state).environmentObject(model)
        }
    }
}
#endif
