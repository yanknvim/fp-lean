# Functional Programming in Lean

> **日本語訳について**：このリポジトリは [leanprover/fp-lean](https://github.com/leanprover/fp-lean) の fork であり、*Functional Programming in Lean* の日本語訳を収録している。翻訳は既定ブランチ `dsv4-ja-translation` にあり、翻訳の範囲・ライセンスについては「[日本語訳について](#日本語訳について)」を参照。

This repository contains the source code of the book Functional Programming in Lean by David Thrane Christiansen.

The original version of the book was released by Microsoft Corporation in 2023 under a Creative Commons Attribution 4.0 International License. The current version has been modified by the author from the original version to account for changes in newer versions of Lean and to use Verso; these changes are copyright 2023-2025 Lean FRO, LLC. A detailed account of the changes can be found in the book's [source code repository](https://github.com/leanprover/fp-lean/).

Generally speaking, the code in this repository is not intended to work on all computers. The purpose of the repository is to produce the book's HTML for readers. In particular, it probably only works on Unix-like systems, due to the way that the built-in tests exercise the programs built in the book. Building the book requires at least a C compiler available as `cc`, with the POSIX headers, and a Unix-like shell.

To build the book, change to the [`book`](book/) directory and run `lake exe fp-lean`. After this, `book/_out/html-multi` contains a multi-page Web version of the book.

To read the book locally, serve that directory over HTTP and open the address that the server prints:

```
lake exe verso-serve
```

## Publishing

The book is published by pushing a tag whose name starts with `release-`. CI builds the tagged commit and deploys it to the production site. Publication happens on `release-` tags alone.

Every other build gets a preview deploy instead: pushes to `master`, pull requests (including those from forks), and manual runs. The preview URL appears as a `netlify/deploy` status on the commit that was built.

The build runs in [`ci.yml`](.github/workflows/ci.yml) and hands the HTML to [`deploy.yml`](.github/workflows/deploy.yml) as an artifact. The credentials live in the deploy workflow, which is what lets a pull request from a fork build and preview.

This fork also publishes the book to GitHub Pages at <https://yanknvim.github.io/fp-lean/>. [`pages.yml`](.github/workflows/pages.yml) builds and deploys every push, and the book is served from the site's root whatever branch it came from, so the most recent deployment is the one that stays. Which branches may publish is not in the workflow: it comes from the deployment branch rules of the `github-pages` environment, a repository setting.

## 日本語訳について

このリポジトリは [leanprover/fp-lean](https://github.com/leanprover/fp-lean) の fork であり、*Functional Programming in Lean* の日本語訳を収録している。翻訳は yanknvim と LLM が行っている。翻訳は既定ブランチ `dsv4-ja-translation` にあり、セクションごとにコミットしているため、訳文の変遷は `git log` で追える。

翻訳の範囲は次のとおり。

- 翻訳しているもの：`book/` の本文（セクション見出し、地の文、脚注、図表のキャプション、演習問題）
- 翻訳していないもの：章タイトル、Lean のコードと識別子、コンパイラの出力例、`examples/` 以下のプログラム

訳語は本文全体で統一するよう努めているが、誤訳や不自然な訳文が残っている可能性がある。見つけた場合は Issues で知らせてほしい。

## ビルド

上流と同じ手順でビルドできる。`book` ディレクトリで `lake exe fp-lean` を実行すると、`book/_out/html-multi` に HTML 版が生成される。

この fork では Nix の開発環境も用意している（[`flake.nix`](flake.nix)）。

```sh
nix develop
build-book     # book/_out/html-multi に HTML を出力
serve-book     # 生成物を HTTP で配信
```

`build-book` は `examples/` のビルドも含む。初回は elan が `book/lean-toolchain` と `examples/lean-toolchain` に書かれたツールチェーンを取得するため、ネットワーク接続が必要である。

## ライセンスと帰属

原著 *Functional Programming in Lean* は 2023 年に Microsoft Corporation が [Creative Commons Attribution 4.0 International License](https://creativecommons.org/licenses/by/4.0/)（CC BY 4.0）の下で公開した。現在の英語版は著者によって、Lean の新しいバージョンに対応し Verso を使うよう変更されており、これらの変更の著作権は 2023-2025 Lean FRO, LLC にある。

本リポジトリはこれを日本語に翻訳したものであり、CC BY 4.0 でいう Adapted Material にあたる。原著者と上流リポジトリを明示し、変更点は git 履歴で確認できる。翻訳は yanknvim と LLM が行い、翻訳部分の著作権は翻訳者に帰属する。ライセンスは上流と同じ CC BY 4.0 を継承する。

