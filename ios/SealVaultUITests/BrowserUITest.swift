// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

// swiftlint:disable force_try

import XCTest

let browserTimeoutSeconds: TimeInterval = 30
let buttonTimeoutSeconds: TimeInterval = 5
let browserAddressBar = "browserAddressBar"

final class BrowserUITest: XCTestCase {

    let ethereumTestUrl = "http://localhost:8080/ethereum.html"
    let newTabTestUrl = "http://localhost:8080/open-new-tab.html"

    func testEthereumDapp() throws {
        let app = try! startBrowserApp()

        enterAddressBar(app, text: ethereumTestUrl)

        tapButton(app, "approveDapp")

        let finishedOk = app.webViews.staticTexts["Finished OK"]
        XCTAssert(finishedOk.waitForExistence(timeout: browserTimeoutSeconds))
    }

    func testOpenNewTab() throws {
        let app = try! startBrowserApp()

        enterAddressBar(app, text: newTabTestUrl)

        app.links["open"].tap()
        let opened = app.webViews.staticTexts["New Tab Target"]
        XCTAssert(opened.waitForExistence(timeout: browserTimeoutSeconds))
    }

    func testOpenDappInBrowser() {
        let app = XCUIApplication()
        app.launch()

        let dapp = "uniswap.org"

        tapButton(app, "Dapps")
        tapButton(app, "Default account")
        print("app.webViews.count", app.webViews.count)

        let uniswapButton = app.buttons["\(dapp) dapp"]
        _ = uniswapButton.waitForExistence(timeout: buttonTimeoutSeconds)
        uniswapButton.press(forDuration: 1)

        tapButton(app, "Open in Browser 2")

        _ = app.buttons["Reload page"].waitForExistence(timeout: buttonTimeoutSeconds)

        let addressBar = app.textFields[browserAddressBar]
        let addressText = addressBar.value as? String
        XCTAssert(addressText?.contains(dapp) ?? false)
    }

    // TODO don't rely on web page loading
    func testBrowserSearch() throws {
        let app = try! startBrowserApp()

        let searchText = "somethingrandom"

        enterAddressBar(app, text: searchText)

        let finishedOk = app.webViews.staticTexts[searchText]
        XCTAssert(finishedOk.waitForExistence(timeout: browserTimeoutSeconds))
    }

    // TODO don't rely on web page loading
    func testPartialUrl() throws {
        let app = try! startBrowserApp()

        enterAddressBar(app, text: "example.com")

        let finishedOk = app.webViews.staticTexts["Example Domain"]
        XCTAssert(finishedOk.waitForExistence(timeout: browserTimeoutSeconds))
    }

    func testErrorLoadingPage() throws {
        let app = try! startBrowserApp()

        enterAddressBar(app, text: "https://doesntexist.sealvault.org")

        let finishedOk = app.webViews.staticTexts["Failed to load page"]
        XCTAssert(finishedOk.waitForExistence(timeout: browserTimeoutSeconds))
    }
}

func startBrowserApp() throws -> XCUIApplication {
    let app = XCUIApplication()
    app.launch()
    tapButton(app, "Browser 1", tabBar: true)
    return app
}

func enterAddressBar(_ app: XCUIApplication, text: String) {
    let addressBar = app.textFields["browserAddressBar"]
    _ = addressBar.waitForExistence(timeout: buttonTimeoutSeconds)

    let pasteMenuItem = app.menuItems.firstMatch
    UIPasteboard.general.string = "Preparing Pasteboard"

    addressBar.tap()
    addressBar.tap()
    _ = pasteMenuItem.waitForExistence(timeout: buttonTimeoutSeconds)

    UIPasteboard.general.string = text
    pasteMenuItem.tap()

    addressBar.tap()
    // new line at end submits. doesn't work if appended to pasted string
    addressBar.typeText("\n")
}

func tapButton(_ app: XCUIApplication, _ accessibilityIdentifier: String, tabBar: Bool = false) {
    let button = tabBar ? app.tabBars.buttons[accessibilityIdentifier] : app.buttons[accessibilityIdentifier]
    _ = button.waitForExistence(timeout: buttonTimeoutSeconds)
    button.tap()
}
