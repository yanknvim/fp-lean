module
public import VersoManual
import FPLean.Examples

import FPLean.HelloWorld.RunningAProgram
import FPLean.HelloWorld.StepByStep
import FPLean.HelloWorld.StartingAProject
import FPLean.HelloWorld.Cat
import FPLean.HelloWorld.Conveniences
import FPLean.HelloWorld.Summary


open Verso.Genre Manual
open Verso Code External

open FPLean


#doc (Manual) "Hello, World!" =>
%%%
tag := "hello-world"
%%%

Leanは、プログラマが使い慣れたテキストエディタから離れずに言語から多くのフィードバックを得られる、豊かな対話環境を持つように設計されている。それと同時に、本物のプログラムを書ける言語でもある。
つまり、バッチ処理用のコンパイラ、ビルドシステム、パッケージマネージャなど、プログラムを書くのに必要な道具がそろっている。

{ref "getting-to-know"}[前の章]ではLeanでの関数型プログラミングの基本を扱った。この章では、プログラミングのプロジェクトを始め、コンパイルし、実行する方法を説明する。
動作して環境とやり取りするプログラム（たとえば標準入力から読み込んだりファイルを作ったりするもの）は、計算を数式の評価と捉える見方とはうまく折り合わない。
この章では、Leanのビルド用ツールの説明に加えて、外界とやり取りする関数型プログラムの考え方を示す。

{include 1 FPLean.HelloWorld.RunningAProgram}

{include 1 FPLean.HelloWorld.StepByStep}

{include 1 FPLean.HelloWorld.StartingAProject}

{include 1 FPLean.HelloWorld.Cat}

{include 1 FPLean.HelloWorld.Conveniences}

{include 1 FPLean.HelloWorld.Summary}
