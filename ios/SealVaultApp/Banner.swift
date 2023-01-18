// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

// Based on: https://stackoverflow.com/a/60088450
// Alternate license to MPL 2.0 for this file: CC BY-SA 4.0

import SwiftUI

struct BannerModifier: ViewModifier {

    @Binding var data: BannerData?

    @State var task: DispatchWorkItem?

    var delay: Double {
        if let data = data {
            return data.durationSeconds
        } else {
            return Config.defaultBannerDurationSeconds
        }
    }

    func hideDelayed() {
        self.task = DispatchWorkItem {
            withAnimation {
                self.data = nil
            }
        }
        DispatchQueue.main.asyncAfter(deadline: .now() + delay, execute: self.task!)
    }

    func body(content: Content) -> some View {
        ZStack {
            if let data = data {
                VStack {
                    HStack {
                        VStack(alignment: .leading, spacing: 2) {
                            Text(data.title)
                                .bold()
                            Text(data.detail)
                                .font(Font.system(size: 15, weight: Font.Weight.light, design: Font.Design.default))
                        }
                        Spacer()
                    }
                    .foregroundColor(Color.white)
                    .padding(12)
                    .background(data.type.tintColor)
                    .cornerRadius(8)
                    .shadow(radius: 20)
                    Spacer()
                }
                .padding()
                .animation(.easeInOut, value: 1.2)
                .transition(AnyTransition.move(edge: .top).combined(with: .opacity))
                // Swipe up to dismiss
                .gesture(DragGesture(minimumDistance: 10, coordinateSpace: .global)
                            .onEnded { value in
                                if value.translation.height < 0 {
                                    withAnimation {
                                        self.data = nil
                                    }
                                }
                            })
                .onChange(of: self.data) { newValue in
                    if let task = self.task, newValue != nil {
                        task.cancel()
                        self.hideDelayed()
                    }
                }
                .onAppear {
                    self.hideDelayed()
                }
                .onDisappear {
                    self.task?.cancel()
                }
                .zIndex(100)
            }
            content
        }
    }
}

extension View {
    func banner(data: Binding<BannerData?>) -> some View {
        self.modifier(BannerModifier(data: data))
    }
}

#if DEBUG
struct Banner_Previews: PreviewProvider {
    static var previews: some View {
        Group {
            BannerPreview(data: BannerData(title: "Title", detail: "Some details", type: .info))
            BannerPreview(data: BannerData(title: "Title", detail: "Some details", type: .success))
            BannerPreview(data: BannerData(title: "Title", detail: "Some details", type: .warning))
            BannerPreview(data: BannerData(title: "Title", detail: "Some details", type: .error))
        }
    }
}

struct BannerPreview: View {
    @State var data: BannerData?

    var body: some View {
        Text("Banner")
            .banner(data: $data)
    }
}
#endif
