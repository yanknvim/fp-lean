# Functional Programming in Lean

This repository contains the source code of the book Functional Programming in Lean by David Thrane Christiansen.

The original version of the book was released by Microsoft Corporation in 2023 under a Creative Commons Attribution 4.0 International License. The current version has been modified by the author from the original version to account for changes in newer versions of Lean and to use Verso; these changes are copyright 2023-2025 Lean FRO, LLC. A detailed account of the changes can be found in the book's [source code repository](https://github.com/leanprover/fp-lean/).

Generally speaking, the code in this repository is not intended to work on all computers. The purpose of the repository is to produce the book's HTML for readers. In particular, it probably only works on Unix-like systems, due to the way that the built-in tests exercise the programs built in the book. Building the book requires at least a C compiler available as `cc`, with the POSIX headers, and a Unix-like shell.

To build the book, change to the [`book`](book/) directory and run `lake exe fp-lean`. After this, `book/_out/html-multi` contains a multi-page Web version of the book.

To read the book locally, serve that directory over HTTP and open the address that the server prints:

```
lake exe verso-serve
```

## Publishing

This fork publishes the book to GitHub Pages at <https://yanknvim.github.io/fp-lean/>. [`pages.yml`](.github/workflows/pages.yml) builds the default branch and deploys the result, so publishing a change means pushing it to that branch. The workflow names no branch: the default branch is a repository setting, and the deployment branch rules of the `github-pages` environment are what the Pages API checks before it accepts a deployment. Pushes anywhere else skip the build and report nothing.

[`ci.yml`](.github/workflows/ci.yml) builds pushes to `master`, release branches, and tags, along with pull requests, and attaches the book HTML to the run as an artifact. Nothing publishes that artifact: it is there to be downloaded and read.

