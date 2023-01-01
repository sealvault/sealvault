// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

import XCTest

final class NativeUITest: XCTestCase {
    func testProfileList() throws {
        // UI tests must launch the application that they test.
        let app = XCUIApplication()
        app.launch()

        tapButton(app, "Profiles (Default is active)", tabBar: true)

        let rowCount = app.collectionViews.element(boundBy: 0).cells.count
        XCTAssert(rowCount >= 1)
    }

    func testCreateProfile() throws {
        let app = XCUIApplication()
        app.launch()

        tapButton(app, "Profiles (Default is active)", tabBar: true)

        tapButton(app, "Edit Profiles")
        tapButton(app, "Add New Profile")

        let profileName = "New Profile Name"
        enterText(app, "Enter Profile Name", text: profileName)
        tapButton(app, "Approve")

        let newProfileButton = app.buttons["\(profileName) profile"]
        XCTAssert(newProfileButton.waitForExistence(timeout: buttonTimeoutSeconds))
    }

    func testSwitchProfile() throws {
        let app = XCUIApplication()
        app.launchArguments = ["-createProfile"]
        app.launch()

        let newProfileButton = app.buttons["New Profile profile"]
        XCTAssert(newProfileButton.waitForExistence(timeout: buttonTimeoutSeconds))
        newProfileButton.press(forDuration: 1)
        tapButton(app, "Set Active")
        var tabProfileIcon = app.buttons["Profiles (New Profile is active)"]
        XCTAssert(tabProfileIcon.waitForExistence(timeout: buttonTimeoutSeconds))

        let defaultPofileButton = app.buttons["Default profile"]
        XCTAssert(defaultPofileButton.waitForExistence(timeout: buttonTimeoutSeconds))
        defaultPofileButton.press(forDuration: 1)
        tapButton(app, "Set Active")
        tabProfileIcon = app.buttons["Profiles (Default is active)"]
        XCTAssert(tabProfileIcon.waitForExistence(timeout: buttonTimeoutSeconds))
    }

//    func testProfileSearch() throws {
//        // UI tests must launch the application that they test.
//        let app = XCUIApplication()
//        app.launch()
//        app.tabBars.buttons["Profiles (Default is active)"].tap()
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
//        // TODO: add this back after we can create profile
//        // Make sure filtering works (fewer rows are displayed after typing than originally)
//        // XCTAssert(rowCount > cells.count)
//
//        // Accept first autocomplete suggestion
//        cells.element(boundBy: 0).tap()
//
//        // Open profile view
//        cells.element(boundBy: 0).tap()
//
//        // Check that profile view was opened by existence of back button to profiles overview
//        let firstNavBarButtonLabel = app.navigationBars.buttons.element(boundBy: 0).label
//        XCTAssert(firstNavBarButtonLabel == "Profiles (Default is active)")
//    }
}
