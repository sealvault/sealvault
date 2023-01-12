// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

;(function SealVaultTest(message) {
  "use strict"

  function setUpTestDisplay() {
    document.body.insertAdjacentHTML(
      "beforeend",
      `
    <div id="tests">
      <h2 id="results" style="background: red">Tests</h2>
      <ul id="test-list"></ul>
    </div>
  `
    )
  }

  function setResult(name, ok) {
    const testList = document.getElementById("test-list")
    const element = document.createElement("li")
    const link = document.createElement("a")
    link.innerText = name
    link.href = `#${name}`
    link.onclick = (e) => {
      e.preventDefault()
      // Have to add manually, otherwise reload fires before setting href from anchor click
      window.location.href = `#${name}`
      window.location.reload()
    }
    element.style.background = ok ? "green" : "red"
    element.appendChild(link)
    testList.appendChild(element)
  }

  window.makeSealVaultTest = async function makeSealVaultTest() {
    const testCases = []
    let failures = 0

    function test(name, func) {
      testCases.push({name, func})
    }

    async function executeTest(name, func) {
      console.debug(`Executing '${name}' test`)
      let ok = false
      try {
        await func(name)
        ok = true
      } catch (e) {
        console.error(`test '${name}' failed with error:`)
        console.error(e)
        console.error(`---`)
      } finally {
        if (!ok) {
          failures += 1
        }
        setResult(name, ok)
      }
    }

    async function executeTests() {
      const onlyName = window.location.hash.replace("#", "")
      const onlyTest = testCases.find(testCase => testCase.name === onlyName)
      if (onlyTest) {
        await executeTest(onlyTest.name, onlyTest.func)
        return
      }

      // Don't rely on awaiting every test definition
      for (let {name, func} of testCases) {
        await executeTest(name, func)
      }

      const success = failures === 0
      if (success) {
        const testsDiv = document.getElementById("results")
        testsDiv.style.background = "green"
      }

      const tests = document.getElementById("tests")
      const resultText = success ? "Finished OK" : "Finished with errors"
      tests.insertAdjacentHTML(
        "beforeend",
        `<h2 id="finished">${resultText}</h2>`
      )
    }

    setUpTestDisplay()

    return { test, executeTests }
  }

  class AssertionError extends Error {
    constructor(message) {
      super(message)
    }
  }

  window.assertArrayEq = function assertEq(a, b) {
    if (JSON.stringify(a) !== JSON.stringify(b)) {
      throw new AssertionError(`Expected the two arrays to be equal: \n${a}\n${b}`)
    }
  }
  window.assertEq = function assertEq(a, b) {
    if (a !== b) {
      throw new AssertionError(`Expected '${a}' and '${b}' to be strictly equal.`)
    }
  }

  window.assert = function assert(truthy, message) {
    if (!truthy) {
      throw new AssertionError(`Assertion failed with message: '${message}'`)
    }
  }
})()
