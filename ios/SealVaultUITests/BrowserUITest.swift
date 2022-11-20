// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

// swiftlint:disable force_try

import XCTest

final class BrowserUITest: XCTestCase {
    var timeOutSeconds: TimeInterval = 30
    let ethereumTestUrl = "http://localhost:8080/ethereum.html"
    let newTabTestUrl = "http://localhost:8080/open-new-tab.html"
    let browserAddressBar = "browserAddressBar"

    func testEthereumDapp() throws {
        let app = try! startBrowserApp()

        let urlField = app.textFields[browserAddressBar]
        enterAddressBar(app, urlField, text: ethereumTestUrl)

        let approveDapp = app.buttons["approveDapp"]
        _ = approveDapp.waitForExistence(timeout: timeOutSeconds)
        approveDapp.tap()

        let finishedOk = app.webViews.staticTexts["Finished OK"]
        XCTAssert(finishedOk.waitForExistence(timeout: timeOutSeconds))
    }

    func testOpenNewTab() throws {
        let app = try! startBrowserApp()

        let urlField = app.textFields[browserAddressBar]
        enterAddressBar(app, urlField, text: newTabTestUrl)

        app.links["open"].tap()
        let opened = app.webViews.staticTexts["New Tab Target"]
        XCTAssert(opened.waitForExistence(timeout: timeOutSeconds))
    }

    // TODO don't rely on web page loading
    func testBrowserSearch() throws {
        let app = try! startBrowserApp()

        let searchText = "somethingrandom"

        let urlField = app.textFields[browserAddressBar]
        enterAddressBar(app, urlField, text: searchText)

        let finishedOk = app.webViews.staticTexts[searchText]
        XCTAssert(finishedOk.waitForExistence(timeout: timeOutSeconds))
    }

    // TODO don't rely on web page loading
    func testPartialUrl() throws {
        let app = try! startBrowserApp()

        let urlField = app.textFields[browserAddressBar]
        enterAddressBar(app, urlField, text: "example.com")

        let finishedOk = app.webViews.staticTexts["Example Domain"]
        XCTAssert(finishedOk.waitForExistence(timeout: timeOutSeconds))
    }

    func testErrorLoadingPage() throws {
        let app = try! startBrowserApp()

        let urlField = app.textFields[browserAddressBar]
        enterAddressBar(app, urlField, text: "https://doesntexist.sealvault.org")

        let finishedOk = app.webViews.staticTexts["Failed to load page"]
        XCTAssert(finishedOk.waitForExistence(timeout: timeOutSeconds))
    }
}

func startBrowserApp() throws -> XCUIApplication {
    let app = XCUIApplication()
    app.launch()
    app.tabBars.buttons["Browser 1"].tap()
    return app
}

func enterAddressBar(_ app: XCUIApplication, _ addressBar: XCUIElement, text: String) {
    let pasteMenuItem = app.menuItems.firstMatch
    UIPasteboard.general.string = "Preparing Pasteboard"

    addressBar.tap()
    addressBar.tap()
    _ = pasteMenuItem.waitForExistence(timeout: 5)

    UIPasteboard.general.string = text
    pasteMenuItem.tap()

    addressBar.tap()
    // new line at end submits. doesn't work if appended to pasted string
    addressBar.typeText("\n")
}
