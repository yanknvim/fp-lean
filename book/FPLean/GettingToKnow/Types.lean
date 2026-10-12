module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

example_module Examples.Intro

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"


#doc (Manual) "Types" =>
%%%
tag := "getting-to-know-types"
%%%

型は、プログラムが計算しうる値に基づいてプログラムを分類する。型はプログラムの中でいくつもの役割を担う。

 1. 値のメモリ上での表現をコンパイラが決めるための手がかりになる。

 2. 関数の入力と出力についての簡潔な仕様として働き、プログラマが意図を他の人に伝える助けになる。コンパイラは、プログラムがこの仕様に従っていることを保証する。

 3. 数値に文字列を足すといった、起こりうるさまざまな間違いを防ぎ、プログラムに必要なテストの数を減らす。

 4. 定型的な記述を減らす補助コードの生成を、Leanコンパイラが自動で行えるようにする。

Leanの型システムは並外れて表現力が高い。
型には、「この整列関数は入力の並べ替えを返す」といった強い仕様も、「この関数は引数の値に応じて戻り値の型が変わる」といった柔軟な仕様も書き表せる。
型システムは、数学の定理を証明するための本格的な論理としても使える。
とはいえ、この先進的な表現力があっても単純な型が不要になるわけではない。より進んだ機能を使うには、まずそうした単純な型を理解しておく必要がある。

:::paragraph
Leanのプログラムは必ず型を持たなければならない。とくに、式は評価する前に型が決まっていなければならない。これまでの例ではLeanが型を自分で見つけられていたが、こちらから指定しなければならないこともある。指定するには、括弧の中でコロン演算子を使う。

```anchor onePlusTwoEval
#eval (1 + 2 : Nat)
```


ここで{anchorName onePlusTwoEval}`Nat`は*自然数*の型であり、精度の制限がない符号なし整数を表す。
Leanでは、負でない整数リテラルの既定の型が{anchorName onePlusTwoEval}`Nat`である。
この既定の型が常に最善とは限らない。
Cでは、引き算の結果が負になるはずのときに、符号なし整数は表現できる最大値に回り込む。
しかし{anchorName onePlusTwoEval}`Nat`はいくらでも大きな符号なしの数を表せるので、回り込む先の最大値が存在しない。
そのため、{anchorName onePlusTwoEval}`Nat`の引き算では、答えが負になるはずの場合に{anchorName Nat}`zero`が返る。
たとえば、

```anchor oneMinusTwoEval
#eval (1 - 2 : Nat)
```

これは{lit}`-1`ではなく{anchorInfo oneMinusTwoEval}`0`と評価される。
負の整数を表せる型を使うには、その型を直接書けばよい。

```anchor oneMinusTwoIntEval
#eval (1 - 2 : Int)
```

この型では、期待どおり{anchorInfo oneMinusTwoIntEval}`-1`という結果になる。
:::

:::paragraph
式を評価せずに型だけを調べるには、{kw}`#eval`の代わりに{kw}`#check`を使う。たとえば、

```anchor oneMinusTwoIntType
#check (1 - 2 : Int)
```

これは引き算を実際には行わずに、{anchorInfo oneMinusTwoIntType}`1 - 2 : Int`と報告する。
:::

:::paragraph
プログラムに型を与えられない場合、{kw}`#check`と{kw}`#eval`のどちらもエラーを返す。たとえば、

```anchor stringAppendList
#check String.append ["hello", " "] "world"
```

出力は次のようになる。

```anchorError stringAppendList
Application type mismatch: The argument
  ["hello", " "]
has type
  List String
but is expected to have type
  String
in the application
  String.append ["hello", " "]
```

{anchorName stringAppendList}`String.append`の最初の引数には文字列が期待されているのに、文字列のリストが渡されたためである。
:::
