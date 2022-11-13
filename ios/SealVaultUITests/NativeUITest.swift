// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import XCTest

final class NativeUITest: XCTestCase {
    func testAccountList() throws {
        // UI tests must launch the application that they test.
        let app = XCUIApplication()
        app.launch()

        let accountsButton = app.tabBars.buttons["Accounts"]
        _ = accountsButton.waitForExistence(timeout: 5)
        accountsButton.tap()

        let rowCount = app.collectionViews.element(boundBy: 0).cells.count
        XCTAssert(rowCount >= 1)
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
