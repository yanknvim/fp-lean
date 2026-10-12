module
public import VersoManual
import FPLean.Examples



open Verso.Genre Manual
open Verso Code External

open FPLean

example_module Examples.Intro

set_option verso.exampleProject "../examples"

set_option verso.exampleModule "Examples.Intro"

#doc (Manual) "Evaluating Expressions" =>
%%%
tag := "evaluating"
%%%


Leanを学ぶプログラマが最初に理解すべきことは、評価がどのように行われるかである。
評価とは、算数で計算するのと同じように、式の値を求める手順である。
たとえば$`15 - 6`の値は$`9`、$`2 × (3 + 1)`の値は$`8`である。
後の式の値を求めるには、まず$`3 + 1`を$`4`に置き換えて$`2 × 4`とし、これをさらに$`8`に簡約する。
数式には変数が含まれることもある。$`x + 1`の値は、$`x`の値が分かるまで計算できない。
Leanでは、プログラムは何よりもまず式であり、計算を考えるときの基本は、式を評価してその値を求めることである。

ほとんどのプログラミング言語は*命令型*であり、プログラムは、結果を得るために順に実行すべき文の並びである。
プログラムは書き換え可能なメモリに触れられるため、変数が指す値は時間とともに変わりうる。
書き換え可能な状態のほかにも、プログラムにはファイルの削除、外部へのネットワーク接続、例外の送出や捕捉、データベースからの読み出しといった副作用がありうる。
「副作用」とは、数式の評価というモデルに当てはまらずにプログラム中で起こりうる事柄を、まとめて指す言葉である。

しかしLeanでは、プログラムは数式と同じように扱う。
変数は、一度値を与えたら別の値を割り当て直せない。式の評価が副作用を起こすこともない。
二つの式の値が等しいなら、一方を他方に置き換えてもプログラムの計算結果は変わらない。
だからといって、Leanで{lit}`Hello, world!`をコンソールに書き出せないわけではない。ただし、入出力を行うことがLeanを使う上での中心的な部分になるわけではない。
そこでこの章では、Leanと対話しながら式を評価する方法を扱う。次の章では、{lit}`Hello, world!`プログラムを書き、コンパイルし、実行する方法を説明する。

:::paragraph
Leanに式を評価させるには、エディタで式の前に{kw}`#eval`を書く。結果はエディタが知らせてくれる。
結果は通常、カーソルかマウスポインタを{kw}`#eval`に合わせると分かる。
たとえば、

```anchor threeEval
#eval 1 + 2
```

これは次のように評価される。

```anchorInfo threeEval
3
```

:::

:::paragraph
Leanは算術演算子について、通常の優先順位と結合性の規則に従う。つまり、

```anchor orderOfOperations
#eval 1 + 2 * 5
```

の値は{anchorInfo orderOfOperationsWrong}`15`ではなく{anchorInfo orderOfOperations}`11`になる。

:::

:::paragraph
普通の数学の記法やほとんどのプログラミング言語では、関数を引数に適用するのに括弧を使う（{lit}`f(x)`など）。Leanは関数を引数の隣に書くだけでよい（{lit}`f x`など）。
関数適用はよく使う操作なので、簡潔に書けることに意味がある。
たとえば、{anchorInfo stringAppendHello}`"Hello, Lean!"`を計算するのに

```
#eval String.append("Hello, ", "Lean!")
```

と書く代わりに、

```anchor stringAppendHello
#eval String.append "Hello, " "Lean!"
```

と書く。関数の二つの引数は、空白で区切って並べるだけでよい。
:::


:::paragraph
算数の計算順序の規則が{anchorTerm orderOfOperationsWrong}`(1 + 2) * 5`という式に括弧を要求するのと同じように、関数の引数を別の関数呼び出しで計算するときにも括弧が要る。
たとえば、次の式には括弧が必要である。

```anchor stringAppendNested
#eval String.append "great " (String.append "oak " "tree")
```

括弧がないと、二つ目の{moduleTerm (anchor := stringAppendNested)}`String.append`が、{moduleTerm (anchor := stringAppendNested)}`"oak "`と{moduleTerm (anchor := stringAppendNested)}`"tree"`を引数として受け取る関数ではなく、一つ目の関数の引数として解釈されてしまうためである。
内側の{anchorTerm stringAppendNested}`String.append`呼び出しの値を先に求める必要があり、それを{moduleTerm (anchor := stringAppendNested)}`"great "`に追加すると、最終的な値{anchorInfo stringAppendNested}`"great oak tree"`になる。
:::

:::paragraph
命令型言語には、しばしば二種類の条件分岐がある。真偽値に応じて実行する命令を選ぶ条件*文*と、真偽値に応じて二つの式のどちらを評価するかを選ぶ条件*式*である。
たとえばCとC++では、条件文は{c}`if`と{c}`else`で書き、条件式は三項演算子で書く。三項演算子では{c}`?`と{c}`:`が条件と分岐を区切る。
Pythonでは、条件文は{python}`if`で始まり、条件式は{python}`if`を途中に置く。
Leanは式を中心とする関数型言語なので、条件文はなく、あるのは条件式だけである。
条件式は{kw}`if`、{kw}`then`、{kw}`else`で書く。
たとえば、

```anchorEvalStep stringAppend 0
String.append "it is " (if 1 > 2 then "yes" else "no")
```

これは次のように評価される。

```anchorEvalStep stringAppend 1
String.append "it is " (if false then "yes" else "no")
```

さらに次のように評価される。

```anchorEvalStep stringAppend 2
String.append "it is " "no"
```

最終的に{anchorEvalStep stringAppend 3}`"it is no"`になる。


:::


:::paragraph
簡潔にするため、このような評価の手順を、間に矢印を挟んで書くことがある。

```anchorEvalSteps stringAppend
String.append "it is " (if 1 > 2 then "yes" else "no")
===>
String.append "it is " (if false then "yes" else "no")
===>
String.append "it is " "no"
===>
"it is no"
```
:::


# 出会うかもしれないメッセージ
%%%
tag := "evaluating-messages"
%%%

:::paragraph
引数が足りない関数適用をLeanに評価させると、エラーメッセージが出る。
たとえば、次の例を考える。

```anchor stringAppendReprFunction
#eval String.append "it is "
```

これはかなり長いエラーメッセージになる。

```anchorError stringAppendReprFunction
Could not synthesize a `ToExpr`, `Repr`, or `ToString` instance for type
  String → String
```

:::

このメッセージが出るのは、Leanの関数が、引数の一部だけを適用された状態では、残りの引数を待つ新しい関数を返すためである。
Leanは関数を利用者に見せられないため、表示しようとするとエラーになる。


# 練習問題
%%%
tag := "evaluating-exercises"
%%%

次の式の値はそれぞれ何か。まず手で計算し、その答えをLeanに入力して確かめてみるとよい。

 * {anchorTerm evalEx}`42 + 19`
 * {anchorTerm evalEx}`String.append "A" (String.append "B" "C")`
 * {anchorTerm evalEx}`String.append (String.append "A" "B") "C"`
 * {anchorTerm evalEx}`if 3 == 3 then 5 else 7`
 * {anchorTerm evalEx}`if 3 == 4 then "equal" else "not equal"`
