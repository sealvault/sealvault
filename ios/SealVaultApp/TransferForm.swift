// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

class TransferState: ObservableObject {
    @Published var account: Account
    @Published var fromAddress: Address
    @Published var token: Token

    @Published var toExternal: String = ""
    @Published var toAddress: Address?
    @Published var showInAppSelection = false

    @Published var disableButton: Bool = false
    @Published var amount: String = ""

    @Published var processing: Bool = false

    var defaultPickerSelection: Address? {
        account.allAddresses.filter({canTransferTo($0)}).first
    }

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

    required init(
        account: Account, token: Token, fromAddress: Address
    ) {
        self.account = account
        self.token = token
        self.fromAddress = fromAddress
    }

    fileprivate func canTransferTo(_ toAddress: Address) -> Bool {
        // TODO: use protocol + chain id and move to address
        return toAddress.chainDisplayName == fromAddress.chainDisplayName && fromAddress.id != toAddress.id
    }
}

struct TransferForm: View {
    @EnvironmentObject var model: GlobalModel
    @ObservedObject var state: TransferState
    // Accessibility size
    @Environment(\.dynamicTypeSize) var size

    var body: some View {
        ScrollView {
            VStack(spacing: 20) {
                Spacer()

                FromSection(state: state)

                ToSection(state: state)

                ChainSection(state: state)

                TokenSection(state: state)

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
        .navigationTitle(Text("Transfer"))
        .dynamicTypeSize(..<DynamicTypeSize.accessibility2)
        .refreshable {
            await state.fromAddress.refreshTokens()
        }
        .sheet(isPresented: $state.showInAppSelection) {
            if let defaultPickerSelection = state.defaultPickerSelection {
                InAppPicker(state: state, pickerSelection: defaultPickerSelection)
                    .presentationDetents([.medium])
                    .background(.ultraThinMaterial)
            }
        }

    }
}

struct FromSection: View {
    @ObservedObject var state: TransferState

    var body: some View {
        GroupBox {
        } label: {
            HStack {
                Text("From")
                Spacer()
                if let dapp = state.account.dappForAddress(address: state.fromAddress) {
                    DappRow(dapp: dapp)
                } else {
                    Text("\(state.account.displayName) Account Wallet")
                }
            }
            .frame(maxWidth: .infinity)
        }
    }
}

struct ToSection: View {
    @ObservedObject var state: TransferState

    @State var toAddressType: ToAddressType = .inApp
    @State var showInAppSelection: Bool = false
    @FocusState private var toExternalFocused: Bool

    enum ToAddressType {
        case inApp
        case external
    }

    var body: some View {
        GroupBox {
            VStack {
                Picker("to", selection: $toAddressType) {
                    Text("🦭 In-App").tag(ToAddressType.inApp)
                    Text("💸 Address").tag(ToAddressType.external)
                }
                .pickerStyle(.segmented)
                .onChange(of: toAddressType) { _ in
                    // Very important to reset otherwise user might mistakenly send to different address
                    state.toExternal = ""
                    state.toAddress = nil
                }

                HStack {
                    switch toAddressType {
                    case .inApp:
                        Button {
                            state.showInAppSelection = true
                        } label: {
                            switch state.toAddress {
                            case .none:
                                Text("Select Dapp or Account Wallet").bold()
                            case .some(let address):
                                if let dapp = state.account.dappForAddress(address: address) {
                                    DappRow(dapp: dapp)
                                } else {
                                    Label {
                                        Text("\(state.account.displayName) Account Wallet").font(.headline)
                                    } icon: {
                                        Image(systemName: "checkmark.circle")
                                    }
                                }
                            }
                        }
                    case .external:
                        VStack {
                            TextField("Paste address here", text: $state.toExternal)
                                .textFieldStyle(.roundedBorder)
                                .frame(maxWidth: .infinity)
                                .autocorrectionDisabled(true)
                                .autocapitalization(.none)
                                .focused($toExternalFocused)
                                .onChange(of: toExternalFocused, perform: { newValue in
                                    state.disableButton = newValue
                                })
                            if !state.toExternal.isEmpty {
                                Text(displayChecksumAddress(state.toExternal))
                            }
                        }
                    }
                }
                .padding(.top, 10)
            }

        } label: {
            HStack {
                Text("To")
            }
        }
    }
}

struct InAppPicker: View {
    @ObservedObject var state: TransferState
    @State var pickerSelection: Address

    @Environment(\.dismiss) var dismiss

    var body: some View {
        VStack(spacing: 20) {
            HStack {
                Text("Select Dapp or Account Wallet").font(.title2)
            }
            .padding(20)

            Spacer()

            Picker("Select Dapp or Account Wallet", selection: $pickerSelection) {
                ForEach(state.account.walletList) { walletAddress in
                    if state.canTransferTo(walletAddress) {
                        Text("\(state.account.displayName) Account Wallet").tag(walletAddress)
                    }
                }
                ForEach(state.account.dappList) { dapp in
                    ForEach(dapp.addressList) { dappAddress in
                        if state.canTransferTo(dappAddress) {
                            Text("\(dapp.humanIdentifier)")
                                .tag(dappAddress)
                        }
                    }
                }
            }
            .pickerStyle(.wheel)

            Spacer()

            VStack(spacing: 20) {
                HStack(spacing: 0) {
                    Button(action: {
                        state.toAddress = nil
                        dismiss()
                    }, label: {
                        Text("Cancel")
                            .frame(maxWidth: .infinity)
                            .foregroundColor(.secondary)
                    })
                    .accessibilityLabel("cancelInAppSelection")
                    .buttonStyle(.borderless)
                    .controlSize(.large)

                    Button(action: {
                        state.toAddress = pickerSelection
                        dismiss()
                    }, label: {
                        Text("OK").frame(maxWidth: .infinity)
                    })
                    .accessibilityLabel("approveInAppSelection")
                    .buttonStyle(.borderless)
                    .controlSize(.large)
                }
            }
        }
    }
}

struct ChainSection: View {
    @ObservedObject var state: TransferState

    var body: some View {
        GroupBox {
        } label: {
            HStack {
                Text("On")
                Spacer()
                Label {
                    Text(state.fromAddress.chainDisplayName)
                } icon: {
                    IconView(image: state.fromAddress.image, iconSize: 24)
                }
            }
            .frame(maxWidth: .infinity)
        }
    }
}

struct TokenSection: View {
    @ObservedObject var state: TransferState

    @FocusState private var amountFocused: Bool

    var body: some View {
        GroupBox {
            VStack {
                HStack {
                    Text("Balance")
                    Spacer()
                    TokenAmount(token: state.token)
                }
                HStack {
                    Text("Amount")
                    Spacer()
                    TextField("Decimal", text: $state.amount)
                        .frame(width: 75)
                        .multilineTextAlignment(.trailing)
                        .textFieldStyle(.roundedBorder)
                        .padding(.leading)
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
            .padding(.top, 10)
        } label: {
            HStack {
                Text("Token")
                Spacer()
                HStack {
                    TokenLabel(token: state.token)
                }
            }
        }
    }
}

struct TransferButton: View {
    let core: AppCoreProtocol
    let cornerRadius: CGFloat = 8

    @ObservedObject var state: TransferState
    @EnvironmentObject var model: GlobalModel

    func makeTransfer() async -> Bool {
        await dispatchBackground(.userInteractive) {
            do {
                if let toAddress = state.toChecksumAddress {
                    if state.token.nativeToken {
                        let args = EthTransferNativeTokenArgs(
                            fromAddressId: state.fromAddress.id, toChecksumAddress: toAddress,
                            amountDecimal: state.amount
                        )
                        try core.ethTransferNativeToken(args: args)
                    } else {
                        let args = EthTransferFungibleTokenArgs(
                            fromAddressId: state.fromAddress.id, toChecksumAddress: toAddress,
                            amountDecimal: state.amount, tokenId: state.token.id
                        )
                        try core.ethTransferFungibleToken(args: args)
                    }
                }
                return true
            } catch CoreError.User(let message) {
                DispatchQueue.main.async {
                    model.bannerData = BannerData(title: "Error transferring token", detail: message, type: .error)
                }
                return false
            } catch CoreError.Retriable(let message) {
                DispatchQueue.main.async {
                    let message = "Something went wrong. Please try again!"
                    model.bannerData = BannerData(title: "Error transferring token", detail: message, type: .error)
                }
                print("Retriable error while transferring token: \(message)")
                return false
            } catch let error {
                DispatchQueue.main.async {
                    let message = "An unexpected error occurred. Please restart the application!"
                    model.bannerData = BannerData(title: "Error transferring token", detail: message, type: .error)
                }
                print("\(error)")
                return false
            }

        }
    }

    var body: some View {
        Button(action: {
            if state.processing {
                return
            }
            state.processing = true
            Task {
                let success = await makeTransfer()
                // Reset amount so that user doesn't submit twice by accident
                state.amount = ""
                state.processing = false
                if success {
                    await state.fromAddress.refreshTokens()
                }
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
        .disabled(state.buttonDisabled)
        .foregroundColor(Color.white)
        .cornerRadius(cornerRadius)
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
        let sucessState = TransferState(account: account, token: walletToken, fromAddress: walletAddress)
        return Group {
            PreviewWrapper(
                model: model,
                state: TransferState(account: account, token: dappToken, fromAddress: dappAddress)
            ).environment(\.dynamicTypeSize, .medium)
            PreviewWrapper(
                model: model,
                state: TransferState(account: account, token: walletToken, fromAddress: walletAddress)
            ).environment(\.dynamicTypeSize, .medium)
            PreviewWrapper(
                model: model,
                state: sucessState
            ).environment(\.dynamicTypeSize, .medium)
            PreviewWrapper(
                model: model,
                state: errorState
            ).environment(\.dynamicTypeSize, .medium)
            PreviewWrapper(
                model: model,
                state: errorState
            ).environment(\.dynamicTypeSize, .accessibility3)

        }
    }

    struct PreviewWrapper: View {
        var model: GlobalModel
        var state: TransferState
        @Environment(\.dynamicTypeSize) var size

        var body: some View {
            TransferForm(state: state)
                .environmentObject(model)
        }
    }
}
#endif
