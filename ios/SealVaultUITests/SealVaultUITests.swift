// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

// swiftlint:disable force_try

import XCTest

class SealVaultUITests: XCTestCase {
    var timeOutSeconds: TimeInterval {
        if ProcessInfo.processInfo.environment["CI"] == "true" {
            return 120
        } else {
            return 30
        }
    }
    let minAccounts = 1
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

    func testAccountList() throws {
        // UI tests must launch the application that they test.
        let app = XCUIApplication()
        app.launch()

        let accountsButton = app.tabBars.buttons["Accounts"]
        _ = accountsButton.waitForExistence(timeout: timeOutSeconds)
        accountsButton.tap()

        let rowCount = app.collectionViews.element(boundBy: 0).cells.count
        XCTAssert(rowCount >= minAccounts)
    }

//    func testAccountSearch() throws {
//        // UI tests must launch the application that they test.
//        let app = XCUIApplication()
//        app.launch()
//        app.tabBars.buttons["Accounts"].tap()
//
//        let cells = app.tables.element(boundBy: 0).cells
//        let rowCount = cells.count
//
//        // Drag down first row to display search bar
//        let firstRow = cells.element(boundBy: 0)
//        let start = firstRow.coordinate(withNormalizedOffset: CGVector(dx: 10, dy: 0))
//        let finish = firstRow.coordinate(withNormalizedOffset: CGVector(dx: 10, dy: 10))
//        start.press(forDuration: 0.01, thenDragTo: finish)
//
//        let searchField = app.searchFields.element(boundBy: 0)
//
//        // Type into the search bar
//        searchField.tap()
//        app.typeText("De")
//
//        // TODO: add this back after we can create account
//        // Make sure filtering works (fewer rows are displayed after typing than originally)
//        // XCTAssert(rowCount > cells.count)
//
//        // Accept first autocomplete suggestion
//        cells.element(boundBy: 0).tap()
//
//        // Open account view
//        cells.element(boundBy: 0).tap()
//
//        // Check that account view was opened by existence of back button to accounts overview
//        let firstNavBarButtonLabel = app.navigationBars.buttons.element(boundBy: 0).label
//        XCTAssert(firstNavBarButtonLabel == "Accounts")
//    }
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

        // Repeatedly delete text as long as there is something in the text field.
        // This is required to clear text that does not fit in to the textfield and is partially hidden initally.
        // Important to check for placeholder value, otherwise it gets into an infinite loop.
        while let stringValue = self.value as? String, !stringValue.isEmpty, stringValue != self.placeholderValue {
            // Move the cursor to the end of the text field
            let lowerRightCorner = self.coordinate(withNormalizedOffset: CGVector(dx: 0.9, dy: 0.9))
            lowerRightCorner.tap()
            let delete = String(repeating: XCUIKeyboardKey.delete.rawValue, count: stringValue.count)
            self.typeText(delete)
        }
    }

    func clearAndEnterText(text: String) {
        self.clear()
        // new line at end submits
        self.typeText("\(text)\n")
    }
}
