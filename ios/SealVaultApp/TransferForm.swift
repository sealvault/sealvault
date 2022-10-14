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
    @Published var errorMessage: BannerData?

    var buttonDisabled: Bool {
        return processing || disableButton || toChecksumAddress == nil || amount == ""
    }

    var toChecksumAddress: String? {
        var toChecksumAddress: String?
        if case .some(value: let addr) = toAddress {
            toChecksumAddress = addr.checksumAddress
        } else if toExternal != "" {
            toChecksumAddress = toExternal
        }
        return toChecksumAddress
    }

    func setErrorMessage(message: String) {
        self.errorMessage = BannerData(title: "Error transferring token", detail: message, type: .error)
    }

    required init(
        account: Account, token: Token, fromAddress: Address
    ) {
        self.account = account
        self.token = token
        self.fromAddress = fromAddress
    }
}

enum ToAddress: Hashable {
    case none
    case some(Address)
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
        .banner(data: self.$state.errorMessage)
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

struct ToSection: View {
    @ObservedObject var state: TransferState

    @State var toAddressType: ToAddressType = .dapp
    @FocusState private var toExternalFocused: Bool

    enum ToAddressType {
        case wallet
        case dapp
        case external
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
                                    .tag(ToAddress.some(wallet))
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
                                        .tag(ToAddress.some(dappAddress))
                                }
                            }
                        }
                    }
                case .external:
                    TextField("Checksum Address", text: $state.toExternal)
                        .textFieldStyle(.roundedBorder)
                        .padding(.horizontal)
                        .autocorrectionDisabled(true)
                        .autocapitalization(.none)
                        .focused($toExternalFocused)
                        .onChange(of: toExternalFocused, perform: { newValue in
                            state.disableButton = newValue
                        })

                }
                Picker("to", selection: $toAddressType) {
                    Text("Wallet").tag(ToAddressType.wallet)
                    Text("Dapp").tag(ToAddressType.dapp)
                    Text("External").tag(ToAddressType.external)
                }
                .pickerStyle(.segmented)
                .onChange(of: toAddressType) { _ in
                    // Very important to reset otherwise user might mistakenly send to different address
                    state.toExternal = ""
                    state.toAddress = ToAddress.none
                }
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
            } catch CoreError.User(let message) {
                DispatchQueue.main.async {
                    self.state.setErrorMessage(message: message)
                }
                return nil
            } catch CoreError.Retriable(let message) {
                DispatchQueue.main.async {
                    self.state.setErrorMessage(message: "Something went wrong. Please try again!")
                }
                print("Retriable error while transferring token: \(message)")
                return nil
            } catch let error {
                DispatchQueue.main.async {
                    self.state.setErrorMessage(message: "An unexpected error occurred. Please restart the application!")
                }
                print("\(error)")
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
        let errorState = TransferState(account: account, token: walletToken, fromAddress: walletAddress)
        errorState.setErrorMessage(message: "test message")
        return Group {
            PreviewWrapper(
                model: model,
                state: TransferState(account: account, token: dappToken, fromAddress: dappAddress)
            )
            PreviewWrapper(
                model: model,
                state: TransferState(account: account, token: walletToken, fromAddress: walletAddress)
            )
            PreviewWrapper(
                model: model,
                state: errorState
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
