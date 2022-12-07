# Changelog

## 2022-12-07

### iOS Beta v0.4.4

#### Improvements

- Allow dismissing banners by swiping up
- 
#### Fixes

- Fix not auto-hiding banners
- Update mint NFT domain to the one that it newly redirects

## 2022-11-28

### iOS Beta v0.4.3

#### Improvements

- Change default dapps to [quickswap.exchange](https://quickswap.exchange/) and [mintnft.today](https://mintnft.today/)

## 2022-11-22

### iOS Beta v0.4.2

#### Improvements

- Increase token transfer amount input field width.
- Increase the number of times we show the default token amount transfer
  disclosure to new users to 5. After they've added 5 new dapps, the disclosure
  is hidden behind an expand button.

#### Fixes

- Fix opening dapp in browser with long press not loading page.

#### Fixes

## 2022-11-18

### iOS Beta v0.4.1

#### Fixes

- Fix address bar not showing due to too many top dapps
- Allow dismissing address bar keyboard by scrolling page down 

### iOS Beta v0.4.0

#### Improvements

- Add top dapps list as default view in browser windows
- Add two dapps by default for new users to help with onboarding
- Streamline transfer form
- Change nav bar title to more legible

## 2022-11-15

## iOS Beta v0.3.3

#### Improvements

- Add chain name to dapp transaction error message on which the error happened.

#### Fixes

- Fix error message display for "insufficient funds for gas * price + value"
  message.

## 2022-11-13

### iOS Beta v0.3.2

#### Improvements

- Change nav tab bar labels to "Browser Tab 1", "Accounts", "Browser Tab 2"
  based on beta feedback.

## 2022-11-09

### iOS Beta v0.3.1

#### Fixes

- Change default home page in in-app web browser due to App Store Review
  requirements.

## 2022-11-01

### iOS Beta v0.3.0

#### Features

- Allow changing connected chain for Ethereum dapps from app. This is important,
because some dapps don't support changing the chain from their UI and just error
out if the user isn't on the expected chain.

#### Fixes

- Fix can't connect [crypto coven](https://cryptocoven.xyz/)

## 2022-10-30

### iOS Beta v0.2.2

#### Improvements

- Add popup banners for feedback about blockchain interactions. This gives users
  more info and lets them switch views while waiting for feedback. Events:
  - Token transfer submitted to mempool success/error.
  - Token transfer confirmed success/error.
  - Dapp allotment transfer success/error.
  - Auto-approved and performed off-chain sig for dapp. Also explains why this 
    is safe.
  - Auto-approved dapp transaction. Also explains why this is safe.
  - Dapp transaction confirmed success/error.
- Improve address view: 
  - Make chains better separated visually. 
  - List mainnets first. 
  - Move address menu to nav bar and put add chain in it.

#### Fixes

- Fix can't connect dHedge [#23](https://github.com/sealvault/sealvault/issues/23)
- Fix can't connect Curve [#24](https://github.com/sealvault/sealvault/issues/24)
- Fix can't connect Hop Exchange [#26](https://github.com/sealvault/sealvault/issues/26)
- Fix default dapp allotment transfer explainer layout.

## 2022-10-24

### iOS Beta v0.2.1

#### Improvements

- Open dapps in browser from account view with long press.
- Add checkbox to disable sending default dapp allotment. Checkbox is hidden
  behind reveal button by default, but it's shown the first three times a user
  adds a dapp.
- Move browser address bar back to bottom as it's more ergonomic.
- Add browser reload and cancel button and only show go forward if available to
  save space.
- Add progress bar to address bar.
- Set Browser 1 home page to [SealVault Discovery
  Page](https://sealvault.org/discover/) and Browser 2 home page to Brave
  Search.
- Add error page to browser.

#### Fixes

- Move dual-tab browsing control to bottom tray and disable swipe to switch
browser windows in order to avoid interfering with website navigation.

## 2022-10-21

### iOS Beta v0.2.0

#### Features

- Dual-tab browsing. Swipe left and right to switch between browser tabs.
- Add new chains to addresses. Only chains hard coded into the application can 
be added. This is because we want to test chains ourselves before we offer them 
to users in the app. We currently support Ethereum (+ Goerli testnet) and 
Polygon Pos (+ Mumbai testnet) but expect more Ethereum chains soon.

#### Improvements

- Rename "Accounts" tab to "Dapps"
- Nest wallet address on different chains under one "Account Wallet" row for
consistent experience with dapp addresses.
- Move current account icon to tab bar so that it's visible in browser mode.
- Set [discover](https://sealvault.org/discover/) as the default home page.

## 2022-10-17

### iOS Beta v0.1.2

#### Improvements

- Add success/error pop ups for token transfer results. 
- Improve token transfer error messages.
- Add default transfer explainer to dapp approval confirmation.
- Make token balance refreshable in transfer form.

#### Fixes

- Fix transfer form layout when text size is increased in iOS accessibility
  settings.
- Fix failure to make fractional token amount transfer on locales that use comma
  decimal separator.

## 2022-10-13

### iOS Beta v0.1.1

#### Improvements

- Add progress spinner when page is loading in browser and reload button when
  it's done loading. The reload button is needed for sites that disable
  scrolling as dragging down to reload doesn't work there.
- Add spinner to transfer form button while request is processing and make it
  green on success.

#### Fixes

- Don't hide browser address bar when scrolling down as it doesn't play well
with websites that manage override default scrolling behaviour.
- Prevent changing the browser address bar text while it's focused.
- Fix dapp icons sometimes getting mixed up in account view.

## 2022-10-11

### iOS Beta v0.1.0

#### Features

- Account, wallet, dapp and token list views
- Single tab web browser with Metamask-compatible [Ethereum Provider JavaScript API.](https://eips.ethereum.org/EIPS/eip-1193)
- Native and fungible token transfer functionality
- [One-Dapp-per-Key](./docs/src/design/one-dapp-per-key.md) implementation
- Ethereum and Polygon PoS token transfer and dapp support
