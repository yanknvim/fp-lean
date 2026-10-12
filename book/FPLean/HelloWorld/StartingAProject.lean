module
public import VersoManual
import FPLean.Examples


open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples/second-lake/greeting"
set_option verso.exampleModule "Main"

#doc (Manual) "Starting a Project" =>
%%%
tag := "starting-a-project"
%%%

Leanで書くプログラムが本格的になってくると、実行ファイルを作る、事前コンパイル方式の流れの方が魅力的になる。
他の言語と同じく、Leanにも複数ファイルのパッケージをビルドし、依存関係を管理する道具がある。
標準のLeanのビルドツールはLake（「Lean Make」の略）という。
Lakeは通常、依存関係とビルド対象を宣言的に書くTOMLファイルで設定する。
より進んだ用途では、LakeをLean自身で設定することもできる。

# 最初の一歩
%%%
tag := "lake-new"
%%%


Lakeを使うプロジェクトを始めるには、{lit}`greeting`というファイルやディレクトリがないディレクトリで{command lake "first-lake"}`lake new greeting`というコマンドを実行する。
すると{lit}`greeting`というディレクトリができ、次のファイルが入る。

 * {lit}`Main.lean`は、Leanコンパイラが{lit}`main`アクションを探すファイルである。
 * {lit}`Greeting.lean`と{lit}`Greeting/Basic.lean`は、プログラムを支えるライブラリの骨組みである。
 * {lit}`lakefile.toml`には、アプリケーションをビルドするために{lit}`lake`が必要とする設定が入っている。
 * {lit}`lean-toolchain`には、そのプロジェクトで使うLeanのバージョンの識別子が入っている。

さらに、{lit}`lake new`はプロジェクトをGitリポジトリとして初期化し、ビルドの途中でできる成果物を無視するよう{lit}`.gitignore`を設定する。
通常、アプリケーションの論理の大部分はプログラム用のライブラリ群に置き、{lit}`Main.lean`には、コマンドラインの解析や中核の論理の実行などを行う小さな包みを書く。
既にあるディレクトリでプロジェクトを作るには、{lit}`lake new`ではなく{lit}`lake init`を実行する。

既定では、ライブラリのファイル{lit}`Greeting/Basic.lean`には定義が一つだけ入っている。
```file lake "first-lake/greeting/Greeting/Basic.lean" "Greeting/Basic.lean"
def hello := "world"
```

ライブラリのファイル{lit}`Greeting.lean`が{lit}`Greeting/Basic.lean`をインポートする。
```file lake "first-lake/greeting/Greeting.lean" "Greeting.lean"
-- This module serves as the root of the `Greeting` library.
-- Import modules here that should be built as part of the library.
import Greeting.Basic
```

つまり、{lit}`Greeting/Basic.lean`で定義したものはすべて、{lit}`Greeting.lean`をインポートするファイルからも使える。
{kw}`import`文では、点はディスク上のディレクトリとして解釈される。

実行ファイルのソース{lit}`Main.lean`には次のように書かれている。
```file lake "first-lake/greeting/Main.lean" "Main.lean"
import Greeting

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
```

{lit}`Main.lean`が{lit}`Greeting.lean`を、{lit}`Greeting.lean`が{lit}`Greeting/Basic.lean`をインポートしているので、{lit}`hello`の定義は{lit}`main`から使える。

パッケージをビルドするには、{command lake "first-lake/greeting"}`lake build`を実行する。
いくつかのビルドの表示が流れたあと、できた実行ファイルは{lit}`.lake/build/bin`に置かれている。
{command lake "first-lake/greeting"}`./.lake/build/bin/greeting`を実行すると、{commandOut lake}`./.lake/build/bin/greeting`が得られる。
実行ファイルを直接動かす代わりに、{lit}`lake exe`コマンドを使えば、必要ならビルドしてから実行してくれる。
{command lake "first-lake/greeting"}`lake exe greeting`を実行しても、{commandOut lake}`lake exe greeting`が得られる。


# Lakefileの設定
%%%
tag := "lakefiles"
%%%

{lit}`lakefile.toml`は*パッケージ*を記述する。パッケージは配布するためのまとまったLeanコードの集まりで、{lit}`npm`や{lit}`nuget`のパッケージ、Rustのクレートに相当する。
パッケージには、ライブラリや実行ファイルをいくつでも入れられる。
Lakeの設定で使える項目は[Lakeのドキュメント](https://lean-lang.org/doc/reference/latest/find/?domain=Verso.Genre.Manual.section&name=lake-config-toml)に書かれている。
生成された{lit}`lakefile.toml`は次のとおりである。
```file lake "first-lake/greeting/lakefile.toml" "lakefile.toml"
name = "greeting"
version = "0.1.0"
defaultTargets = ["greeting"]

[[lean_lib]]
name = "Greeting"

[[lean_exe]]
name = "greeting"
root = "Main"
```


この最初のLakeの設定は三つの項目から成る。
 * ファイルの先頭にある*パッケージ*の設定、
 * {lit}`Greeting`という名前の*ライブラリ*の宣言、そして
 * {lit}`greeting`という名前の*実行ファイル*である。

Lakeの設定ファイルには、パッケージはちょうど一つだけ書き、依存関係、ライブラリ、実行ファイルはいくつでも書ける。
慣例として、パッケージと実行ファイルの名前は小文字で始め、ライブラリの名前は大文字で始める。
依存関係は、他のLeanパッケージ（ローカルのものか、リモートのGitリポジトリのもの）の宣言である。
Lakeの設定ファイルの項目では、ソースファイルの場所、モジュールの階層、コンパイラのフラグなどを設定できる。
ただし一般に、既定の設定は妥当である。
Leanの形式で書いたLakeの設定ファイルには、さらに次のものを書ける。*外部ライブラリ*は、Leanで書かれていないライブラリで、できあがる実行ファイルに静的リンクする。*カスタムターゲット*は、ライブラリと実行ファイルの分類にうまく当てはまらないビルド対象である。*スクリプト*は、本質的には{moduleName}`IO`アクション（{moduleName}`main`に似ている）だが、加えてパッケージの設定についての情報にアクセスできる。

ライブラリ、実行ファイル、カスタムターゲットをまとめて*ターゲット*と呼ぶ。
既定では、{lit}`lake build`は{lit}`defaultTargets`のリストに指定されたターゲットをビルドする。
既定でないターゲットをビルドするには、{lit}`lake build`の後ろにターゲットの名前を引数として指定する。

# ライブラリとインポート
%%%
tag := "libraries-and-imports"
%%%

Leanのライブラリは、階層的に整理されたソースファイルの集まりから成り、そこから名前をインポートできる。このファイルを*モジュール*と呼ぶ。
既定では、ライブラリにはその名前と一致するルートファイルが一つある。
ここでは、ライブラリ{lit}`Greeting`のルートファイルは{lit}`Greeting.lean`である。
{lit}`Main.lean`の最初の行である{moduleTerm}`import Greeting`が、{lit}`Greeting.lean`の中身を{lit}`Main.lean`で使えるようにする。

ライブラリにモジュールを追加するには、{lit}`Greeting`というディレクトリを作り、その中にファイルを置く。
それらの名前は、ディレクトリの区切りを点に置き換えてインポートできる。
たとえば、{lit}`Greeting/Smile.lean`というファイルを次の内容で作ると、
```file lake "second-lake/greeting/Greeting/Smile.lean" "Greeting/Smile.lean"
def Expression.happy : String := "a big smile"
```

{lit}`Main.lean`から次のようにその定義を使える。
```file lake "second-lake/greeting/Main.lean" "Main.lean"
import Greeting
import Greeting.Smile

open Expression

def main : IO Unit :=
  IO.println s!"Hello, {hello}, with {happy}!"
```


モジュール名の階層と名前空間の階層は別物である。
Leanでは、モジュールはコードを配布する単位であり、名前空間はコードを整理する単位である。
つまり、モジュール{lit}`Greeting.Smile`で定義した名前が、自動的に{lit}`Greeting.Smile`という名前空間に入るわけではない。
とくに、{moduleName (module:=Greeting.Smile) (show:=happy)}`Expression.happy`は{lit}`Expression`名前空間に属する。
モジュールは名前をどの名前空間に置いてもよく、それをインポートするコードは名前空間を{kw}`open`してもよい。
{kw}`import`はソースファイルの中身を使えるようにするものであり、{kw}`open`は名前空間の名前を修飾なしで現在の文脈で使えるようにするものである。

{moduleTerm}`open Expression`という行により、{moduleName (module:=Greeting.Smile)}`Expression.happy`という名前を{moduleName}`main`から{moduleName}`happy`として使えるようになる。
名前空間は*選択的に*開くこともでき、その一部の名前だけを修飾なしで使えるようにできる。
そのためには、使いたい名前を括弧の中に書く。
たとえば{moduleTerm (module:=Aux)}`Nat.toFloat`は自然数を{moduleTerm (module:=Aux)}`Float`に変換する。
{moduleTerm (module:=Aux)}`open Nat (toFloat)`と書けば、{moduleName (module:=Aux)}`toFloat`として使えるようになる。
