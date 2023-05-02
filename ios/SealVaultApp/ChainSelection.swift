// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import SwiftUI

struct ChainSelection: View {
    @State var title: String = "Select Network"
    var onSubmit: (_ newChainId: UInt64) async -> Void

    @EnvironmentObject private var model: GlobalModel
    @State var chains: [CoreEthChain] = []
    @State var selectedChain: CoreEthChain?
    @Environment(\.dismiss) var dismiss

    var body: some View {
        VStack(spacing: 20) {
            SheetTitle(title: title)

            Spacer()

            if let chain = chains.first {
                ChainPicker(chains: $chains, selectedChain: $selectedChain, pickerSelection: chain)
            }

            Spacer()

            VStack(spacing: 20) {
                HStack(spacing: 0) {
                    Button(action: {
                        dismiss()
                    }, label: {
                        Text("Cancel")
                            .frame(maxWidth: .infinity)
                            .foregroundColor(.secondary)
                    })
                    .accessibilityLabel("Reject Add Chain")
                    .buttonStyle(.borderless)
                    .controlSize(.large)

                    Button(action: {
                        Task {
                            if let chain = selectedChain {
                                await onSubmit(chain.chainId)
                            } else {
                                print("No chain selected")
                            }
                            dismiss()
                        }
                    }, label: {
                        Text("OK").frame(maxWidth: .infinity)
                    })
                    .accessibilityLabel("Approve Add Chain")
                    .buttonStyle(.borderless)
                    .controlSize(.large)
                }
            }
        }
        .task {
            self.chains = await self.model.listEthChains()
            if let chain = self.chains.first {
                self.selectedChain = chain
            }
        }
    }
}

// Workaround for picker not taking optional binding without "None" option
struct ChainPicker: View {
    @Binding var chains: [CoreEthChain]
    @Binding var selectedChain: CoreEthChain?
    @State var pickerSelection: CoreEthChain

    var body: some View {
        Picker("Chains", selection: $pickerSelection) {
            ForEach(chains) { chain in
                Text(chain.displayName).tag(chain)
            }
        }
        .pickerStyle(.wheel)
        .onChange(of: pickerSelection) { newValue in
            selectedChain = newValue
        }
    }
}

#if DEBUG
struct AddChain_Previews: PreviewProvider {
    static var previews: some View {
        let model = GlobalModel.buildForPreview()

        ChainSelection { newChaind in
            print("onSubmit new chain id: \(newChaind)")
        }.environmentObject(model)
    }
}
#endif
