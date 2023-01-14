// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

/**
 * The in-page providers are designed to have no dependencies for security reasons.
 * The source is separated into modules with native JavaScript
 * closures in order to avoid the complexity and security considerations
 * of introducing a JavaScript build tool to an Xcode project.
 * Some modules depend on other modules, therefore it's important to
 * preserve their order within this source file.
 *
 * Targets iOS 15 Safari.
 *
 */
;(function SealVaultProviders() {
  "use strict"

  // The values for the placeholders are injected by the app provider when the page is
  // loaded.

  // Must not be nested property
  const SEALVAULT_RPC_PROVIDER = "<SEALVAULT_RPC_PROVIDER>"
  // Can be nested property
  const SEALVAULT_REQUEST_HANDLER = "<SEALVAULT_REQUEST_HANDLER>"
  // 0x prefixed hex format
  const SEALVAULT_DEFAULT_CHAIN_ID = "<SEALVAULT_DEFAULT_CHAIN_ID>"
  // Decimal integer string
  const SEALVAULT_DEFAULT_NETWORK_VERSION = "<SEALVAULT_DEFAULT_NETWORK_VERSION>"

  const ETHEREUM_PROVIDER = "ethereum"
  const REQUEST_TIMEOUT_MS = 60 * 1000

  /**
   * Get a potentially nested property from object.
   *
   * Based on: https://stackoverflow.com/a/6906859
   *
   * @param obj A JavaScript object with string keys.
   * @param propString A key or nested keys eg. "key" or "key.nested.more"
   * @returns The parent object and the value of the property or undefined if it
   * doesn't exist.
   */
  function getPropByString(obj, propString) {
    if (!propString) {
      return obj
    }

    const props = propString.split(".")
    const iLen = props.length - 1
    let i = 0
    let parent
    for (; i < iLen; i += 1) {
      const prop = props[i]

      let candidate = obj[prop]
      if (candidate !== undefined) {
        parent = obj
        obj = candidate
      } else {
        break
      }
    }
    return {
      parent: obj,
      value: obj[props[i]],
    }
  }

  /**
   * Convert an utf-8 string encoded as hex bytes to a string.
   *
   * Based on: https://stackoverflow.com/a/43131635
   *
   * @param hexStr The utf-8 string encoded as hex bytes.
   * @returns The string.
   */
  function hexBytesToString(hexStr) {
    const ints = hexStr.match(/[\da-f]{2}/gi).map((h) => parseInt(h, 16))
    const bytes = new Uint8Array(ints)
    return new TextDecoder().decode(bytes)
  }

  /**
   * Generate a cryptographically random v4 UUID.
   *
   * From: https://stackoverflow.com/a/2117523
   *
   * @returns The uuid as string.
   */
  function uuidV4() {
    // Expands to '10000000-1000-4000-8000-100000000000'
    const template = [1e7] + -1e3 + -4e3 + -8e3 + -1e11
    return template.replace(/[018]/g, (c) =>
      (c ^ (crypto.getRandomValues(new Uint8Array(1))[0] & (15 >> (c / 4)))).toString(16)
    )
  }

  /**
   * Create an event emitter object.
   */
  function makeEventEmitter() {
    const state = {
      listeners: new Map(),
    }

    /**
     * Partial implementation of the NodeJS EventEmitter class.
     * https://nodejs.org/api/events.html#class-eventemitter
     *
     * @namespace EventEmitter
     */
    const eventEmitter = {
      /**
       * Add a listener for an event.
       *
       * @param {string|symbol} eventName
       * @param {Function} listener
       * @returns {EventEmitter}
       */
      on(eventName, listener) {
        if (!state.listeners.has(eventName)) {
          state.listeners.set(eventName, [])
        }

        const listenerArray = state.listeners.get(eventName)
        listenerArray.push(listener)

        return this
      },
      /**
       * Synchronously call listeners registered for the event.
       *
       * @param {string|symbol} eventName
       * @param  {...any} args The args passed to the listeners.
       * @returns {EventEmitter}
       */
      emit(eventName, ...args) {
        if (!state.listeners.has(eventName)) {
          return this
        }

        const listenerArray = state.listeners.get(eventName)
        listenerArray.forEach((listener) => {
          try {
            listener.apply(this, args)
          } catch (error) {
            // Throw the error outside the current call stack.
            setTimeout(() => {
              throw error
            })
          }
        })

        return this
      },

      /**
       * Removes at most one reference to the listener from the
       * event listeners for the event.
       *
       * @param {string|Symbol} eventName
       * @param {Function} listener
       * @returns {EventEmitter}
       */
      removeListener(eventName, listener) {
        if (!state.listeners.has(eventName)) {
          return this
        }

        const listenerArray = state.listeners.get(eventName)
        const index = listenerArray.indexOf(listener)
        if (index > -1) {
          listenerArray.splice(index, 1)
        }

        return this
      },

      /**
       * Removes all listeners, or those of the specified eventName.
       *
       * @param {[string|Symbol]} eventName
       * @returns {EventEmitter}
       */
      removeAllListeners(eventName) {
        if (eventName === undefined) {
          state.listeners = new Map()
        } else {
          state.listeners.delete(eventName)
        }
        return this
      },
    }

    return Object.freeze(eventEmitter)
  }

  /**
   * Ethereum provider that is injected into web pages to expose transaction
   * signing functionality from the SealVault iOS app to dapps.
   *
   * Supports
   * [EIP-1193](https://eips.ethereum.org/EIPS/eip-1193): provider object and events spec
   * [EIP-747](https://eips.ethereum.org/EIPS/eip-747): wallet_watchAsset (TODO)
   * [EIP-3085](https://eips.ethereum.org/EIPS/eip-3085): wallet_addEthereumChain
   * [EIP-3326](https://ethereum-magicians.org/t/eip-3326-wallet-switchethereumchain/5471): wallet_switchEthereumChain
   *
   */
  ;(function EthereumProvider() {

    console.debug(`Initializing ${EthereumProvider.name}`)

    /**
     * EIP-1193 Provider error object: https://github.com/ethereum/EIPs/blob/master/EIPS/eip-1193.md#rpc-errors
     */
    class ProviderRpcError extends Error {
      constructor(error) {
        let { code, data, message } = error
        // Server error
        code = code ?? -32000
        if (!message) {
          message = `JSONRPC Error ${code} ${
            data ? " - " + JSON.stringify(data, null, 2) : ""
          }`
        }
        super(message)
        this.code = code
        this.data = data
      }
    }

    EthereumProvider.modules = {}

    EthereumProvider.modules.sealVaultRpc = (function SealVaultRpcProvider() {
      // Map from request id to promise resolvers
      const requests = new Map()

      /**
       * The SealVault iOS app sends responses to the in-page provider via this object.
       * It is not meant to be accessed by third parties, but it's exposed on the window
       * object. No additional security controls are introduced to prevent unintended access
       * to this object, as defending a dapp from malicious code running on its website
       * is out of scope.
       *
       * @namespace SealVaultRpc
       */
      const sealVaultRpc = {
        /**
         * Perform an RPC request to the SealVault iOS app.
         *
         * @param {Object} jsonRpcRequest  - The JSON RPC request object.
         * @returns {Promise}
         */
        request(jsonRpcRequest) {
          console.debug('sv request', jsonRpcRequest)
          const requestPromise = new Promise((resolve, reject) => {
            const { parent, value: requestHandler } = getPropByString(
              window,
              SEALVAULT_REQUEST_HANDLER
            )
            try {
              requestHandler.call(parent, JSON.stringify(jsonRpcRequest))
            } catch (e) {
              console.error(`SealVault RPC provider failed to call request handler: ${e}`)
              reject(new ProviderRpcError({ message: e.toString() }))
              return
            }
            requests.set(jsonRpcRequest.id, { resolve, reject })
          })

          const timeout = new Promise((resolve, reject) =>
            window.setTimeout(() => {
              console.error(`SealVault RPC request id ${jsonRpcRequest.id} timed out.`)
              requests.delete(jsonRpcRequest.id)
              reject(new ProviderRpcError({ message: "Timeout" }))
            }, REQUEST_TIMEOUT_MS)
          )

          return Promise.race([requestPromise, timeout])
        },

        /**
         * The SealVault app uses this to respond to in-page-requests.
         *
         * @param {String} responseHex  - The message object as hexadecimal utf-8 bytes.
         * @returns undefined
         */
        respond(responseHex) {
          let response
          try {
            // Prevent reflected XSS by passing the result as hexadecimal utf-8 bytes to JS.
            // See the security model in the developer docs for more.
            response = JSON.parse(hexBytesToString(responseHex))
            console.debug('sv response', response)
          } catch (error) {
            // We don't know which request to respond to
            console.error(
              `SealVault RPC provider failed to parse response: ${responseHex}`
            )
            return
          }
          const resolvers = requests.get(response.id)
          if (!resolvers) {
            console.error(
              `SealVault RPC provider got unknown request id in response: ${response}`
            )
            return
          }
          if (response.error) {
            resolvers.reject(new ProviderRpcError(response.error))
          } else {
            resolvers.resolve(response.result)
          }
        },

        /**
         * The SealVault app can use this to notify the in-page provider about an
         * [EIP-1193](https://eips.ethereum.org/EIPS/eip-1193#events) event.
         *
         * See [EIP-1193](https://eips.ethereum.org/EIPS/eip-1193#events) for
         * specification of each event.
         *
         * @param {String} messageHex  - The message object as hexadecimal utf-8 bytes.
         * @returns undefined
         */
        notify(messageHex) {
          const message = JSON.parse(hexBytesToString(messageHex))
          EthereumProvider.modules.internalEvents.emit(message.event, message.data)
        },
      }

      return Object.freeze(sealVaultRpc)
    })()

    // Needed because clients can remove event emitters from the `window.ethereum`
    EthereumProvider.modules.internalEvents = makeEventEmitter()

    EthereumProvider.modules.ethereum = (function EthereumProviderInterface() {
      /**
       *
       * An [EIP-1193 Ethereum Provider.](https://eips.ethereum.org/EIPS/eip-1193
       *
       * Supports widely used [MetaMask legacy interfaces.](https://docs.metamask.io/guide/ethereum-provider.html#table-of-contents)
       *
       * Based on: [@metamask/providers](https://github.com/MetaMask/providers)
       * See NOTICE.md in the repository root for copyright notice.
       *
       */

      const state = {
        isConnected: true,
        chainId: SEALVAULT_DEFAULT_CHAIN_ID,
        networkVersion: SEALVAULT_DEFAULT_NETWORK_VERSION,
        selectedAddress: null,
      }

      /**
       * Alias for ethereum.request({ method: 'eth_requestAccounts' }).
       */
      function enable() {
        return request({ method: "eth_requestAccounts" })
      }

      /**
       * Returns whether the provider can process RPC requests.
       *
       * @memberof Ethereum
       * @returns {boolean}
       */
      function isConnected() {
        return state.isConnected
      }

      /**
       * Submits an RPC request for the given method, with the given params.
       * Resolves with the result of the method call, or rejects on error.
       *
       * @memberof Ethereum
       * @param {Object} args  - The RPC request arguments.
       * @param {string} args.method - The RPC method name.
       * @param {Array|Object|undefined} args.params - The parameters for the RPC method.
       * @returns {Promise} A Promise that resolves with the result of the RPC method,
       * or rejects if an error is encountered.
       */
      async function request(args) {
        const jsonRpcRequest = {
          jsonrpc: "2.0",
          id: uuidV4(),
          method: args.method,
          params: args.params,
        }
        return EthereumProvider.modules.sealVaultRpc.request(jsonRpcRequest)
      }

      /**
       * MetaMask legacy interface: https://docs.metamask.io/guide/ethereum-provider.html#legacy-methods
       *
       * @memberof Ethereum
       * @param {Object} jsonRpcRequest  - The JSON RPC request object.
       * @param {Function} callback  - The callback with an error as first argument or
       * JSON RPC response as second argument if there was no error.
       * @returns {void}
       */
      function sendAsync(jsonRpcRequest, callback) {
        EthereumProvider.modules.sealVaultRpc
          .request(jsonRpcRequest)
          // Catch is first to not catch error from callback.
          .catch((error) => callback(error, null))
          .then((result) => callback(null, result))
      }

      /**
       * MetaMask legacy interface: https://docs.metamask.io/guide/ethereum-provider.html#legacy-methods
       *
       * @memberof Ethereum
       * @param {String|Object} methodOrPayload  - The JSON RPC method or request object.
       * @param {Function|Array<unknown>} paramsOrCallback  - The callback with an error as first argument or
       * JSON RPC response as second argument if there was no error.
       * @returns {void|Promise}
       */
      function send(methodOrPayload, paramsOrCallback) {
        if (
          methodOrPayload &&
          typeof methodOrPayload.method === "string" &&
          paramsOrCallback &&
          typeof paramsOrCallback === "function"
        ) {
          return sendAsync(methodOrPayload, paramsOrCallback)
        } else if (typeof methodOrPayload === "string") {
          return request({ method: methodOrPayload, params: paramsOrCallback })
        } else {
          // The third signature of `send` requires synchronous RPC calls which we can't
          // support.
          throw new Error(`Unsupported signature for ethereum.send`)
        }
      }

      /**
       * The Ethereum provider object is injected by the SealVault app into web pages to facilitate transactions on EVM-compatible chains.
       * Implements [EIP-1193](https://eips.ethereum.org/EIPS/eip-1193) and widely used legacy [MetaMask interfaces](https://docs.metamask.io/guide/ethereum-provider.html#table-of-contents)
       *
       * @namespace Ethereum
       * @property {boolean} isMetaMask - Indicating that this provider is a MetaMask provider.
       * @property {string|null} chainId - The chain ID of the currently connected Ethereum chain. See [chainId.network]{@link https://chainid.network} for more information.
       * @property {string|null} networkVersion - ???
       * @property {string|null} selectedAddress - The user's currently selected Ethereum address. If null, MetaMask is either locked or the user has not permitted any addresses to be viewed.
       */
      const ethereum = Object.create(makeEventEmitter(), {
        // Properties are enumerable for MetaMask provider compatibility,
        // as it uses public class members, but otherwise restricted.
        isMetaMask: {
          value: true,
          enumerable: true,
        },
        // Metamask exposes experimental APIs here.
        // The bnc-onboard package uses this property to test for MM: https://github.com/blocknative/web3-onboard/blob/4ecba80f215c55aeb9fd3903936bdcee7200758e/src/utilities.ts#L378
        _metamask: {
          value: {},
          enumerable: true,
        },
        chainId: {
          get() {
            return state.chainId
          },
          enumerable: true,
        },
        networkVersion: {
          get() {
            return state.networkVersion
          },
          enumerable: true,
        },
        selectedAddress: {
          get() {
            return state.selectedAddress
          },
          enumerable: true,
        },
        enable: {
          value: enable,
        },
        isConnected: {
          value: isConnected,
        },
        request: {
          value: request,
        },
        send: {
          value: send,
        },
        sendAsync: {
          value: sendAsync,
        },
      })

      EthereumProvider.modules.internalEvents.on(
        "sealVaultConnect",
        ({ chainId, networkVersion, selectedAddress }) => {
          if (state.chainId !== chainId) {
            EthereumProvider.modules.internalEvents.emit("chainChanged", chainId)
          }

          if (state.networkVersion !== networkVersion) {
            EthereumProvider.modules.internalEvents.emit("networkChanged", networkVersion)
          }

          // Don't trigger "accountsChanged" event as that causes infinite reload
          // on https://fi.woo.org/
          state.selectedAddress = selectedAddress
        }
      )

      // We never send this event in the current implementation, only here for
      // completeness.
      EthereumProvider.modules.internalEvents.on("disconnected", (error) => {
        console.error(error)
        state.isConnected = false
        ethereum.emit("disconnected", error)
        ethereum.emit("close", error)
      })

      EthereumProvider.modules.internalEvents.on("chainChanged", (chainId) => {
        state.chainId = chainId
        ethereum.emit("chainChanged", chainId)
        // MetaMask legacy event
        ethereum.emit("chainIdChanged", chainId)
      })

      EthereumProvider.modules.internalEvents.on("networkChanged", (networkVersion) => {
        state.networkVersion = networkVersion
        ethereum.emit("networkChanged", networkVersion)
      })

      // We never send this in the current implementation, only here for
      // completeness.
      EthereumProvider.modules.internalEvents.on("accountsChanged", (accounts) => {
        state.selectedAddress = accounts[0]
        ethereum.emit("accountsChanged", accounts)
      })

      // Some providers try to mutate the ethereum object. In case they try to mutate a
      // property, we should silently ignore it to emulate MetaMask behaviour. We won't
      // freeze, as MetaMask doesn't freeze the object.
      // https://github.com/MetaMask/providers/blob/57953b105dd9d3eecbb8d639fd64859da450062c/src/initializeInpageProvider.ts#L52
      return new Proxy(ethereum, {
        deleteProperty: () => true,
      })
    })()

    // Expose certain modules globally

    // The SealVault RPC provider is called from Swift
    Object.defineProperty(window, SEALVAULT_RPC_PROVIDER, {
      value: EthereumProvider.modules.sealVaultRpc,
    })

    if (window[ETHEREUM_PROVIDER]) {
      console.warn(
        `${EthereumProvider.name}: 'window.${ETHEREUM_PROVIDER}' is already defined, it will be overwritten.`
      )
    }

    // The Ethereum provider is called by the dapp front end
    Object.defineProperty(window, ETHEREUM_PROVIDER, {
      value: EthereumProvider.modules.ethereum,
      writable: false,
      // MetaMask defines it as enumerable
      enumerable: true,
    })
  })()
})()
