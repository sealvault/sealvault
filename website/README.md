# SealVault Website

## Overview

URL: [https://sealvault.org](https://sealvault.org)

Provides [landing page](https://sealvault.org) and features for end users,
[developer documentation](https://sealvault.org/dev-docs/) for SealVault
developers and the [SealVault blog.](https://sealvault.org/blog/)

Powered by [Material for
MkDocs](https://squidfunk.github.io/mkdocs-material/).

## Development

The blog and privacy features used by the site used to require [Mkdocs Material
Insiders,](https://squidfunk.github.io/mkdocs-material/insiders/) but they are
part of the free community edition now, so no license is needed to build the
site.

Install the dependencies and serve the site locally with
[pipenv:](https://pipenv.pypa.io/)

```sh
pipenv install
pipenv run mkdocs serve
```

Note that the `privacy` plugin downloads external assets (web fonts, MathJax)
at build time, so the first build needs network access.

## Deployment

Pushes to the main branch automatically deploy the website to
[https://sealvault.org](https://sealvault.org) by Netlify.

[Deploy previews](https://docs.netlify.com/site-deploys/deploy-previews/) are
enabled for PRs and branches in the `sealvault/sealvault` repo are automatically
deployed to `https://{branch-name}--sealvault.netlify.app`.

## License

<span xmlns:dct="http://purl.org/dc/terms/" property="dct:title">Copyright (c) SealVault Inc 2023. The website content is licensed under a <a rel="license" href="http://creativecommons.org/licenses/by/4.0/">Creative Commons Attribution 4.0 International License</a>.
