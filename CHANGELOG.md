# Changelog

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
