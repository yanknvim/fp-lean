module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"


#doc (Manual) "Functions and Definitions" =>
%%%
tag := "functions-and-definitions"
%%%

:::paragraph
Leanでは、定義は{kw}`def`キーワードで導入する。
たとえば{anchorTerm helloNameVal}`hello`という名前が文字列{anchorTerm helloNameVal}`"Hello"`を指すように定義するには、次のように書く。

```anchor hello
def hello := "Hello"
```

Leanでは、新しい名前の定義には{anchorTerm helloNameVal}`=`ではなくコロンと等号の演算子{anchorTerm hello}`:=`を使う。
{anchorTerm helloNameVal}`=`は既存の式どうしが等しいことを表すのに使うためである。二つの演算子を使い分けると混乱を避けられる。
:::

:::paragraph
{anchorTerm helloNameVal}`hello`の定義では、式{anchorTerm helloNameVal}`"Hello"`が単純なので、Leanが定義の型を自動で決められる。
しかし、ほとんどの定義はそれほど単純ではないので、通常は型を書く必要がある。
定義する名前の後ろにコロンを付けて書く。

```anchor lean
def lean : String := "Lean"
```

:::

:::paragraph
名前を定義したので、使えるようになった。したがって、

```anchor helloLean
#eval String.append hello (String.append " " lean)
```

と出力される。

```anchorInfo helloLean
"Hello Lean"
```

Leanでは、定義した名前はその定義より後でしか使えない。
:::

多くの言語では、関数の定義は他の値の定義とは違う構文を使う。
たとえばPythonでは、関数の定義は{kw}`def`キーワードで始まり、他の定義は等号で書く。
Leanでは、関数も他の値と同じ{kw}`def`キーワードで定義する。
とはいえ、{anchorTerm helloNameVal}`hello`のような定義が導入する名前は、呼び出されるたびに同じ結果を返す引数なしの関数ではなく、*その値そのもの*を直接指す。

# 関数の定義
%%%
tag := "defining-functions"
%%%

:::paragraph
Leanで関数を定義する方法はいくつかある。最も単純なのは、関数の引数を定義の型の前に、空白で区切って並べる方法である。 たとえば、引数に1を足す関数は次のように書ける。

```anchor add1
def add1 (n : Nat) : Nat := n + 1
```

この関数を{kw}`#eval`で試すと、期待どおり{anchorInfo add1_7}`8`になる。

```anchor add1_7
#eval add1 7
```

:::

:::paragraph
複数の引数に関数を適用するのに引数の間に空白を書くのと同じように、複数の引数を受け取る関数は、引数の名前と型の間に空白を書いて定義する。 二つの引数のうち大きい方を結果とする関数{anchorName maximum}`maximum`は、{anchorName Nat}`n`と{anchorName maximum}`k`という二つの{anchorName maximum}`Nat`の引数を取り、{anchorName maximum}`Nat`を返す。

```anchor maximum
def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else n
```

同様に、関数{anchorName spaceBetween}`spaceBetween`は二つの文字列を空白でつないで返す。

```anchor spaceBetween
def spaceBetween (before : String) (after : String) : String :=
  String.append before (String.append " " after)
```

:::

:::paragraph
{anchorName maximum_eval}`maximum`のような定義済みの関数に引数を渡すと、まず本体の中で引数の名前を渡された値で置き換え、次にその本体を評価して結果が決まる。 For example:

```anchorEvalSteps maximum_eval
maximum (5 + 8) (2 * 7)
===>
maximum 13 14
===>
if 13 < 14 then 14 else 13
===>
14
```

:::

自然数、整数、文字列に評価される式は、それぞれそうを示す型（{anchorName Nat}`Nat`、{anchorName Positivity}`Int`、{anchorName Book}`String`）を持つ。
関数も同じである。
{anchorName Nat}`Nat`を受け取って{anchorName Bool}`Bool`を返す関数の型は{anchorTerm evenFancy}`Nat → Bool`であり、二つの{anchorName Nat}`Nat`を受け取って{anchorName Nat}`Nat`を返す関数の型は{anchorTerm currying}`Nat → Nat → Nat`である。

特別な場合として、関数の名前をそのまま{kw}`#check`に渡すと、Leanは関数のシグネチャを返す。
{anchorTerm add1sig}`#check add1`と入力すると、{anchorInfo add1sig}`add1 (n : Nat) : Nat`が得られる。
ただし、関数の名前を括弧で囲むと、関数が普通の式として扱われるので、Leanに関数の型を表示させられる。{anchorTerm add1type}`#check (add1)`は{anchorInfo add1type}`add1 : Nat → Nat`を、{anchorTerm maximumType}`#check (maximum)`は{anchorInfo maximumType}`maximum : Nat → Nat → Nat`を返す。
この矢印はASCIIの代替矢印{anchorTerm add1typeASCII}`->`でも書けるので、先ほどの関数の型はそれぞれ{anchorTerm add1typeASCII}`example : Nat -> Nat := add1`、{anchorTerm maximumTypeASCII}`example : Nat -> Nat -> Nat := maximum`と書ける。

舞台裏では、すべての関数は引数をちょうど一つだけ取る。
{anchorName maximum3Type}`maximum`のように複数の引数を取るように見える関数も、実際には引数を一つ取って新しい関数を返す関数である。
その新しい関数が次の引数を取り、引数がなくなるまでこれが続く。
複数引数の関数に引数を一つだけ渡すと、これが分かる。{anchorTerm maximum3Type}`#check maximum 3`は{anchorInfo maximum3Type}`maximum 3 : Nat → Nat`を、{anchorTerm stringAppendHelloType}`#check spaceBetween "Hello "`は{anchorInfo stringAppendHelloType}`spaceBetween "Hello " : String → String`を返す。
関数を返す関数を使って複数引数の関数を実装することを、数学者Haskell Curryにちなんで*カリー化*と呼ぶ。
関数の矢印は右結合なので、{anchorTerm currying}`Nat → Nat → Nat`は{anchorTerm currying}`Nat → (Nat → Nat)`と括弧を付けたのと同じである。

## 練習問題
%%%
tag := "function-definition-exercises"
%%%

 * 最初の引数を二番目と三番目の引数の間に入れた新しい文字列を作る、型{anchorTerm joinStringsWith}`String → String → String → String`の関数{anchorName joinStringsWithEx}`joinStringsWith`を定義せよ。{anchorEvalStep joinStringsWithEx 0}`joinStringsWith ", " "one" "and another"`は{anchorEvalStep joinStringsWithEx 1}`"one, and another"`と評価されるはずである。
 * {anchorTerm joinStringsWith}`joinStringsWith ": "`の型は何か。自分の答えをLeanで確かめよ。
 * 与えられた高さ、幅、奥行きを持つ直方体の体積を計算する、型{anchorTerm volume}`Nat → Nat → Nat → Nat`の関数{anchorName volume}`volume`を定義せよ。

# 型の定義
%%%
tag := "defining-types"
%%%

型付きのプログラミング言語の多くには、Cの{c}`typedef`のように型の別名を定義する手段がある。
しかしLeanでは、型は言語の第一級の要素であり、他の式と同じく式である。
つまり、定義は他の値と同じように型を参照できる。

:::paragraph
たとえば、{anchorName StringTypeDef}`String`と打つのが面倒なら、短い別名{anchorName StringTypeDef}`Str`を定義できる。

```anchor StringTypeDef
def Str : Type := String
```

すると、定義の型に{anchorName StringTypeDef}`String`の代わりに{anchorName aStr}`Str`を使える。

```anchor aStr
def aStr : Str := "This is a string."
```

:::

これがうまくいくのは、型がLeanの他の部分と同じ規則に従うためである。
型は式であり、式の中では定義済みの名前をその定義で置き換えられる。
{anchorName aStr}`Str`は{anchorName Book}`String`を意味するものとして定義したので、{anchorName aStr}`aStr`の定義は意味をなす。

## 出会うかもしれないメッセージ
%%%
tag := "abbrev-vs-def"
%%%

:::paragraph
型に定義を使う実験をややこしくするのが、Leanが整数リテラルのオーバーロードに対応していることである。
{anchorName NaturalNumberTypeDef}`Nat`が短すぎるなら、長い名前{anchorName NaturalNumberTypeDef}`NaturalNumber`を定義できる。

```anchor NaturalNumberTypeDef
def NaturalNumber : Type := Nat
```

しかし、定義の型に{anchorName NaturalNumberTypeDef}`Nat`の代わりに{anchorName NaturalNumberTypeDef}`NaturalNumber`を使うと、期待した効果が得られない。
とくに、次の定義は、

```anchor thirtyEight
def thirtyEight : NaturalNumber := 38
```

次のエラーになる。

```anchorError thirtyEight
failed to synthesize instance of type class
  OfNat NaturalNumber 38
numerals are polymorphic in Lean, but the numeral `38` cannot be used in a context where the expected type is
  NaturalNumber
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

:::

このエラーは、Leanが数値リテラルの*オーバーロード*を許すために起こる。
適切な場合には、あたかも組み込みの型であるかのように、新しい型にも自然数のリテラルを使える。
これは数学を扱いやすく表せるようにするというLeanの目標の一部であり、数学の分野ごとに数の記法をまったく違う目的で使うためでもある。
このオーバーロードを可能にする機能は、オーバーロードを探す前にすべての定義済みの名前を定義で置き換えるわけではない。これが上のエラーメッセージにつながる。

:::paragraph
この制限を避ける方法の一つは、定義の右辺で{anchorName thirtyEightFixed}`Nat`という型を指定し、{anchorTerm thirtyEightFixed}`38`に{anchorName thirtyEightFixed}`Nat`のオーバーロードの規則を使わせることである。

```anchor thirtyEightFixed
def thirtyEight : NaturalNumber := (38 : Nat)
```

この定義も型としては正しい。{anchorEvalStep NaturalNumberDef 0}`NaturalNumber`は定義により{anchorEvalStep NaturalNumberDef 1}`Nat`と同じ型だからである。
:::

別の解決策は、{anchorName NaturalNumberDef}`Nat`のものと同じように働くオーバーロードを{anchorName NaturalNumberDef}`NaturalNumber`に対して定義することである。
ただし、これにはLeanのより進んだ機能が必要である。

:::paragraph
最後に、{anchorName NaturalNumberDef}`Nat`の新しい名前を{kw}`def`ではなく{kw}`abbrev`で定義すると、オーバーロードの解決時に定義済みの名前をその定義で置き換えられる。
{kw}`abbrev`で書いた定義は常に展開される。
たとえば、

```anchor NTypeDef
abbrev N : Type := Nat
```

および

```anchor thirtyNine
def thirtyNine : N := 39
```

は問題なく受け入れられる。
:::

舞台裏では、オーバーロードの解決時に展開できるものとして内部的に印を付けられた定義と、そうでない定義がある。
展開すべき定義を*還元可能*と呼ぶ。
還元可能性を制御できることは、Leanを大規模に使うために欠かせない。すべての定義を完全に展開すると、型が非常に大きくなり、機械の処理が遅くなり、利用者にも理解しにくくなる。
{kw}`abbrev`で作った定義には還元可能という印が付く。
