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
        urlField.enterText(text: ethereumTestUrl)

        let approveDapp = app.buttons["approveDapp"]
        _ = approveDapp.waitForExistence(timeout: timeOutSeconds)
        approveDapp.tap()

        let finishedOk = app.webViews.staticTexts["Finished OK"]
        XCTAssert(finishedOk.waitForExistence(timeout: timeOutSeconds))
    }

    func testOpenNewTab() throws {
        let app = try! startBrowserApp()

        let urlField = app.textFields[browserAddressBar]
        urlField.enterText(text: newTabTestUrl)

        app.links["open"].tap()
        let opened = app.webViews.staticTexts["New Tab Target"]
        XCTAssert(opened.waitForExistence(timeout: timeOutSeconds))
    }

    // TODO don't rely on web page loading
    func testBrowserSearch() throws {
        let app = try! startBrowserApp()

        let searchText = "somethingrandom"

        let urlField = app.textFields[browserAddressBar]
        urlField.enterText(text: searchText)

        let finishedOk = app.webViews.staticTexts[searchText]
        XCTAssert(finishedOk.waitForExistence(timeout: timeOutSeconds))
    }

    // TODO don't rely on web page loading
    func testPartialUrl() throws {
        let app = try! startBrowserApp()

        let urlField = app.textFields[browserAddressBar]
        urlField.enterText(text: "example.com")

        let finishedOk = app.webViews.staticTexts["Example Domain"]
        XCTAssert(finishedOk.waitForExistence(timeout: timeOutSeconds))
    }

    func testErrorLoadingPage() throws {
        let app = try! startBrowserApp()

        let urlField = app.textFields[browserAddressBar]
        urlField.enterText(text: "https://doesntexist.sealvault.org")

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

extension XCUIElement {
    func enterText(text: String) {
        self.tap()
        // new line at end submits
        self.typeText("\(text)\n")
    }
}
