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
        urlField.clearAndEnterText(text: ethereumTestUrl)

        let approveDapp = app.buttons["approveDapp"]
        _ = approveDapp.waitForExistence(timeout: timeOutSeconds)
        approveDapp.tap()

        let finishedOk = app.webViews.staticTexts["Finished OK"]
        XCTAssert(finishedOk.waitForExistence(timeout: timeOutSeconds))
    }

    func testOpenNewTab() throws {
        let app = try! startBrowserApp()

        let urlField = app.textFields[browserAddressBar]
        urlField.clearAndEnterText(text: newTabTestUrl)

        app.links["open"].tap()
        let opened = app.webViews.staticTexts["New Tab Target"]
        XCTAssert(opened.waitForExistence(timeout: timeOutSeconds))
    }

    // TODO don't rely on web page loading
    func testBrowserSearch() throws {
        let app = try! startBrowserApp()

        let searchText = "somethingrandom"

        let urlField = app.textFields[browserAddressBar]
        urlField.clearAndEnterText(text: searchText)

        let finishedOk = app.webViews.staticTexts[searchText]
        XCTAssert(finishedOk.waitForExistence(timeout: timeOutSeconds))
    }

    // TODO don't rely on web page loading
    func testPartialUrl() throws {
        let app = try! startBrowserApp()

        let urlField = app.textFields[browserAddressBar]
        urlField.clearAndEnterText(text: "example.com")

        let finishedOk = app.webViews.staticTexts["Example Domain"]
        XCTAssert(finishedOk.waitForExistence(timeout: timeOutSeconds))
    }
}

func startBrowserApp() throws -> XCUIApplication {
    let app = XCUIApplication()
    app.launch()
    app.tabBars.buttons["Browser"].tap()
    return app
}

extension XCUIElement {
    /// Removes any current text in the field before typing in the new value and submitting
    /// Based on: https://stackoverflow.com/a/32894080
    func clear() {
        if self.value as? String == nil {
            XCTFail("Tried to clear and enter text into a non string value")
            return
        }

        // Make sure keyboard is fully visible before we start deleting text, otherwise lower right corner tap below
        // may be inaccurate.
        self.tap()
        _ = XCUIApplication().keyboards.element.waitForExistence(timeout: 2)

        // Repeatedly delete text as long as there is something in the text field.
        // This is required to clear text that does not fit in to the textfield and is partially hidden initally.
        // Important to check for placeholder value, otherwise it gets into an infinite loop.
        while let stringValue = self.value as? String, !stringValue.isEmpty, stringValue != self.placeholderValue {
            // Move the cursor to the end of the text field
            let lowerRightCorner = self.coordinate(withNormalizedOffset: CGVector(dx: 0.9, dy: 0.9))
            lowerRightCorner.tap()
            let delete = String(repeating: XCUIKeyboardKey.delete.rawValue, count: stringValue.count)
            self.typeText(delete)
            // Make sure we read up-to-date self.value
            Thread.sleep(forTimeInterval: TimeInterval(floatLiteral: 0.1))
        }
    }

    func clearAndEnterText(text: String) {
        self.clear()
        // new line at end submits
        self.typeText("\(text)\n")
    }
}
