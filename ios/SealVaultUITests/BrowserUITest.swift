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
    let cookieTestUrl = "http://localhost:8080/cookie-test.html"

    func testEthereumDapp() throws {
        let app = try! startBrowserApp()

        enterAddressBar(app, text: ethereumTestUrl)

        tapButton(app, "Approve")

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
        let app = try! startBrowserApp(createSecondProfile: true, switchToBrowser: false)

        // Set other profile active to test that the app switches the active profile when dapp is
        // launched from inactive profile.
        setActiveProfile(app, profileName: "CLI Profile")

        let dapp = "quickswap.exchange"

        tapButton(app, "Profiles (CLI Profile is active)", tabBar: true)
        tapButton(app, "Default profile")

        let quickswapButton = app.buttons["\(dapp) dapp"]
        _ = quickswapButton.waitForExistence(timeout: buttonTimeoutSeconds)
        quickswapButton.press(forDuration: 1)

        tapButton(app, "Open in Right Browser")

        _ = app.buttons["Reload page"].waitForExistence(timeout: buttonTimeoutSeconds)

        let addressBar = app.textFields[browserAddressBar]
        let addressText = addressBar.value as? String
        // Test that dapp was loaded in the browser
        XCTAssert(addressText?.contains(dapp) ?? false)

        // Test that active profile was switched to Default
        let profilesButton = app.tabBars.buttons["Profiles (Default is active)"]
        XCTAssert(profilesButton.waitForExistence(timeout: buttonTimeoutSeconds))
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

        enterAddressBar(app, text: "sealvault.org")

        let finishedOk = app.webViews.staticTexts["SealVault"]
        XCTAssert(finishedOk.waitForExistence(timeout: browserTimeoutSeconds))
    }

    func testErrorLoadingPage() throws {
        let app = try! startBrowserApp()

        enterAddressBar(app, text: "https://doesntexist.sealvault.org")

        let finishedOk = app.webViews.staticTexts["Failed to load page"]
        XCTAssert(finishedOk.waitForExistence(timeout: browserTimeoutSeconds))
    }

    func testClearHistoryOnProfileSwitch() throws {
        let app = try! startBrowserApp(createSecondProfile: true, switchToBrowser: false)

        setActiveProfile(app, profileName: "CLI Profile")

        tapButton(app, "Left Browser", tabBar: true)
        // Sets the cookie on first load
        enterAddressBar(app, text: cookieTestUrl)
        // No cookie before first load
        var noCookie = app.webViews.staticTexts["No cookie"]
        XCTAssert(noCookie.waitForExistence(timeout: browserTimeoutSeconds))

        // There should be a cookie on the second load
        tapButton(app, "Reload page")
        let hasCookie = app.webViews.staticTexts["Has cookie"]
        XCTAssert(hasCookie.waitForExistence(timeout: browserTimeoutSeconds))

        tapButton(app, "Profiles (CLI Profile is active)", tabBar: true)
        // This should clear browser history
        setActiveProfile(app, profileName: "Default")

        tapButton(app, "Left Browser", tabBar: true)
        enterAddressBar(app, text: cookieTestUrl)
        // So there should be no cookie when loaded for the first time with a different profile
        noCookie = app.webViews.staticTexts["No cookie"]
        XCTAssert(noCookie.waitForExistence(timeout: browserTimeoutSeconds))
    }
}

func startBrowserApp(createSecondProfile: Bool = false, switchToBrowser: Bool = true) throws -> XCUIApplication {
    let app = XCUIApplication()
    if createSecondProfile {
        app.launchArguments = ["-createProfile"]
    }
    app.launch()
    if switchToBrowser {
        tapButton(app, "Left Browser", tabBar: true)
    }
    return app
}

func enterText(_ app: XCUIApplication, _ textFieldName: String, text: String) {
    let textField = app.textFields[textFieldName]
    _ = textField.waitForExistence(timeout: buttonTimeoutSeconds)

    let pasteMenuItem = app.menuItems.firstMatch
    UIPasteboard.general.string = "Preparing Pasteboard"

    textField.tap()
    textField.tap()
    _ = pasteMenuItem.waitForExistence(timeout: buttonTimeoutSeconds)

    UIPasteboard.general.string = text
    pasteMenuItem.tap()

    textField.tap()
    // new line at end submits. doesn't work if appended to pasted string
    textField.typeText("\n")
}

func enterAddressBar(_ app: XCUIApplication, text: String) {
    enterText(app, "browserAddressBar", text: text)
}

func tapButton(_ app: XCUIApplication, _ accessibilityIdentifier: String, tabBar: Bool = false) {
    let button = tabBar ? app.tabBars.buttons[accessibilityIdentifier] : app.buttons[accessibilityIdentifier]
    _ = button.waitForExistence(timeout: buttonTimeoutSeconds)
    button.tap()
}
