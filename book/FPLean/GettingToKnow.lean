module
public import VersoManual
import FPLean.Examples
import FPLean.GettingToKnow.Evaluating
import FPLean.GettingToKnow.Types
import FPLean.GettingToKnow.FunctionsDefinitions
import FPLean.GettingToKnow.Structures
import FPLean.GettingToKnow.Strings
import FPLean.GettingToKnow.DatatypesPatterns
import FPLean.GettingToKnow.Polymorphism
import FPLean.GettingToKnow.Conveniences
import FPLean.GettingToKnow.Summary

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Hello"


#doc (Manual) "Getting to Know Lean" =>
%%%
tag := "getting-to-know"
%%%

伝統にならえば、プログラミング言語の紹介は、コンソールに{moduleTerm}`"Hello, world!"`を表示するプログラムをコンパイルして実行するところから始めるものとされている。
この単純なプログラムは、言語のツール一式が正しくインストールされ、コンパイルしたコードを実行できることを確かめる役割を果たす。

しかし、1970年代以降、プログラミングは変わった。
現在では、コンパイラはテキストエディタに組み込まれているのが普通であり、プログラムを書いている最中に環境がフィードバックを返してくれる。
Leanも例外ではない。Language Server Protocolを拡張した実装を持ち、テキストエディタと通信して、利用者が入力するそばからフィードバックを返す。

Python、Haskell、JavaScriptなど、さまざまな言語にはread-eval-print-loop（REPL）がある。対話的なトップレベルやブラウザのコンソールとも呼ばれ、式や文を入力できる。
入力すると、言語がその結果を計算して表示する。
一方Leanは、こうした機能をエディタとのやり取りに取り込んでいる。コマンドを書くと、テキストエディタがプログラム本文に重ねてフィードバックを表示する。
この章では、エディタ上でLeanを操作する方法を短く紹介する。コマンドラインからバッチ的にLeanを使う伝統的な方法は{ref "hello-world"}[Hello, World!]で説明する。

エディタでLeanを開いたまま本書を読み、各例を打ち込みながら進めるのがよい。掲載した例を
 いろいろと触って、何が起きるか見てみてほしい。

{include 1 FPLean.GettingToKnow.Evaluating}

{include 1 FPLean.GettingToKnow.Types}

{include 1 FPLean.GettingToKnow.FunctionsDefinitions}

{include 1 FPLean.GettingToKnow.Structures}

{include 1 FPLean.GettingToKnow.DatatypesPatterns}

{include 1 FPLean.GettingToKnow.Polymorphism}

{include 1 FPLean.GettingToKnow.Strings}

{include 1 FPLean.GettingToKnow.Conveniences}

{include 1 FPLean.GettingToKnow.Summary}
