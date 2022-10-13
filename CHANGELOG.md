# Changelog

## 2022-10-13

### iOS Beta v0.1.1

#### Fixes

- Don't hide browser address bar when scrolling down as it doesn't play well
with websites that manage override default scrolling behaviour.
- Add progress spinner when page is loading in browser and reload button when 
it's done loading. The reload button is needed for sites that disable scrolling
as dragging down to reload doesn't work there.
- Prevent changing the browser address bar text while it's focused.
- Add spinner to transfer form button while request is processing and make it
green on success.
- Fix dapp icons sometimes getting mixed up in account view.

## 2022-10-11

### iOS Beta v0.1.0

#### Features

- Account, wallet, dapp and token list views
- Single tab web browser with Metamask-compatible [Ethereum Provider JavaScript API.](https://eips.ethereum.org/EIPS/eip-1193)
- Native and fungible token transfer functionality
- [One-Dapp-per-Key](./docs/src/design/one-dapp-per-key.md) implementation
- Ethereum and Polygon PoS token transfer and dapp support
