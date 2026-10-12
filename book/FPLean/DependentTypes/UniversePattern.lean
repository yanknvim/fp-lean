module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.DependentTypes.Finite"

#doc (Manual) "The Universe Design Pattern" =>
%%%
tag := "universe-pattern"
%%%

Leanでは、他の型を分類する{anchorTerm sundries}`Type`、{anchorTerm sundries}`Type 3`、{anchorTerm sundries}`Prop`のような型を宇宙と呼ぶ。
しかし*宇宙*という語は、データ型を使ってLeanの型の部分集合を表し、関数でそのデータ型のコンストラクタを実際の型に変換する設計パターンにも使う。
このデータ型の値を、その型の*コード*と呼ぶ。

Leanに組み込みの宇宙と同じく、このパターンで実装した宇宙も、使える型のある集まりを記述する型である。ただしその仕組みは異なる。
Leanには、他の型を直接記述する{anchorTerm sundries}`Type`、{anchorTerm sundries}`Type 3`、{anchorTerm sundries}`Prop`のような型がある。
この仕組みを{deftech}*ラッセル流の宇宙*と呼ぶ。
この節で述べる利用者が定義する宇宙は、その型をすべて*データ*として表し、それらのコードを実際の紛れもない型として解釈する明示的な関数を含む。
この仕組みを{deftech}*タルスキ流の宇宙*と呼ぶ。
依存型理論に基づくLeanのような言語はほとんど常にラッセル流の宇宙を使うが、タルスキ流の宇宙はそうした言語でAPIを定義するのに役に立つパターンである。

独自の宇宙を定義すると、APIで使える型の閉じた集まりを切り出せる。
型の集まりが閉じているので、コードについての再帰により、プログラムがその宇宙の*どの*型でも働くようにできる。
独自の宇宙の一例は、{anchorName NatOrBool}`Nat`を表すコード{anchorName NatOrBool}`nat`と、{anchorName NatOrBool}`Bool`を表すコード{anchorName NatOrBool}`bool`を持つ。

```anchor NatOrBool
inductive NatOrBool where
  | nat | bool

abbrev NatOrBool.asType (code : NatOrBool) : Type :=
  match code with
  | .nat => Nat
  | .bool => Bool
```
コードでパターンマッチングすると型を洗練できる。{moduleName (module := Examples.DependentTypes)}`Vect`のコンストラクタでパターンマッチングすると期待される長さを洗練できるのと同じである。
たとえば、この宇宙の型を文字列から復元するプログラムは次のように書ける。

```anchor decode
def decode (t : NatOrBool) (input : String) : Option t.asType :=
  match t with
  | .nat => input.toNat?
  | .bool =>
    match input with
    | "true" => some true
    | "false" => some false
    | _ => none
```
{anchorName decode}`t`についての依存パターンマッチングにより、期待される結果の型{anchorTerm decode}`t.asType`がそれぞれ{anchorTerm natOrBoolExamples}`NatOrBool.nat.asType`と{anchorTerm natOrBoolExamples}`NatOrBool.bool.asType`に洗練され、これらは実際の型{anchorName NatOrBool}`Nat`と{anchorName NatOrBool}`Bool`に計算される。

他のデータと同じく、コードは再帰的でもよい。
{anchorName NestedPairs}`NestedPairs`型は、組と自然数の型のあらゆる入れ子をコード化する。

```anchor NestedPairs
inductive NestedPairs where
  | nat : NestedPairs
  | pair : NestedPairs → NestedPairs → NestedPairs

abbrev NestedPairs.asType : NestedPairs → Type
  | .nat => Nat
  | .pair t1 t2 => asType t1 × asType t2
```
この場合、解釈の関数{anchorName NestedPairs}`NestedPairs.asType`は再帰的である。
つまり、この宇宙の{anchorName NestedPairsbeq}`BEq`を実装するには、コードについての再帰が要る。

```anchor NestedPairsbeq
def NestedPairs.beq (t : NestedPairs) (x y : t.asType) : Bool :=
  match t with
  | .nat => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd

instance {t : NestedPairs} : BEq t.asType where
  beq x y := t.beq x y
```

{anchorName beqNoCases}`NestedPairs`宇宙のどの型にもすでに{anchorName beqNoCases}`BEq`インスタンスがあるが、型クラスの探索はインスタンス宣言でデータ型の起こりうる場合をすべて自動で調べるわけではない。{anchorName beqNoCases}`NestedPairs`のように、そうした場合が無限にありうるからである。
コードについての再帰でそれらを見つける方法をLeanに説明するのではなく、{anchorName beqNoCases}`BEq`インスタンスに直接訴えようとするとエラーになる。
```anchor beqNoCases
instance {t : NestedPairs} : BEq t.asType where
  beq x y := x == y
```
```anchorError beqNoCases
failed to synthesize instance of type class
  BEq t.asType

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
エラーメッセージの{anchorName beqNoCases}`t`は、型{anchorName beqNoCases}`NestedPairs`の未知の値を表す。

# 型クラスと宇宙の比較
%%%
tag := "type-classes-vs-universe-pattern"
%%%

型クラスは、必要なインターフェースの実装があれば、際限のない型の集まりをAPIで使えるようにする。
ほとんどの場合、これのほうが好ましい。
APIの用途をあらかじめすべて予想するのは難しく、型クラスは、作者が予想したより多くの型でライブラリのコードを使えるようにする便利な手段である。

一方、タルスキ流の宇宙は、APIを使えるのをあらかじめ決めた型の集まりだけに制限する。
これはいくつかの場面で役に立つ。
 * 渡された型によって関数がまったく違う働きをすべきとき。型そのものではパターンマッチングできないが、型のコードならパターンマッチングできる。
 * 外部のシステムが与えられるデータの型を本質的に制限しており、余分な柔軟さを望まないとき
 * いくつかの操作の実装に加えて、型のさらなる性質が要求されるとき

型クラスは、JavaやC#のインターフェースが役に立つ多くの場面で役に立つ。一方タルスキ流の宇宙は、封印クラスを使うような場面で、しかし普通の帰納的データ型が使えない場合に役に立ちうる。

# 有限型の宇宙
%%%
tag := "finite-type-universe"
%%%

APIで使える型をあらかじめ決めた集まりに制限すると、際限のないAPIでは不可能な操作が可能になる。
たとえば、関数は通常、等しさを比べられない。
関数は、同じ入力に対して同じ出力を返すときに等しいと見なすべきである。
これを調べるには無限の時間がかかりうる。型{anchorTerm sundries}`Nat → Bool`の二つの関数を比べるには、ありとあらゆる{anchorName sundries}`Nat`について同じ{anchorName sundries}`Bool`を返すかを調べねばならないからである。

言い換えれば、無限の型からの関数はそれ自体が無限である。
関数は表と見なせ、引数の型が無限である関数は、各場合を表すのに無限に行が必要になる。
しかし有限の型からの関数は、その表に有限の行しか要らず、有限である。
引数の型が有限である二つの関数は、起こりうる引数をすべて数え上げ、それぞれについて関数を呼び、その結果を比べることで等しさを調べられる。
高階の関数の等しさを調べるには、与えられた型の起こりうる関数をすべて生成する必要があり、そのためには戻り値の型も有限である必要がある。引数の型の各要素を戻り値の型の各要素に対応させられるようにするためである。
これは*速い*方法ではないが、有限の時間で終わる。

有限の型を表す一つの方法は宇宙によるものである。

```anchor Finite
inductive Finite where
  | unit : Finite
  | bool : Finite
  | pair : Finite → Finite → Finite
  | arr : Finite → Finite → Finite

abbrev Finite.asType : Finite → Type
  | .unit => Unit
  | .bool => Bool
  | .pair t1 t2 => asType t1 × asType t2
  | .arr dom cod => asType dom → asType cod
```
この宇宙で、コンストラクタ{anchorName Finite}`arr`は関数型を表し、これは{anchorName Finite}`arr`ow（矢印）で書く。

:::paragraph
この宇宙の二つの値の等しさを比べるのは、{anchorName NestedPairs}`NestedPairs`宇宙の場合とほとんど同じである。
唯一の重要な違いは{anchorName Finite}`arr`の場合が加わっていることで、{anchorName FiniteAll}`Finite.enumerate`という補助関数を使って{anchorName FiniteBeq}`dom`がコード化する型の値をすべて生成し、ありとあらゆる入力について二つの関数が等しい結果を返すかを調べる。

```anchor FiniteBeq
def Finite.beq (t : Finite) (x y : t.asType) : Bool :=
  match t with
  | .unit => true
  | .bool => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd
  | .arr dom cod =>
    dom.enumerate.all fun arg => beq cod (x arg) (y arg)
```
標準ライブラリの{anchorName sundries}`List.all`関数は、与えられた関数がリストのどの要素でも{anchorName sundries}`true`を返すかを調べる。
この関数を使って、ブール値上の関数の等しさを比べられる。
```anchor arrBoolBoolEq
#eval Finite.beq (.arr .bool .bool) (fun _ => true) (fun b => b == b)
```
```anchorInfo arrBoolBoolEq
true
```
標準ライブラリの関数を比べるのにも使える。
```anchor arrBoolBoolEq2
#eval Finite.beq (.arr .bool .bool) (fun _ => true) not
```
```anchorInfo arrBoolBoolEq2
false
```
関数の合成のような道具を使って組み立てた関数まで比べられる。
```anchor arrBoolBoolEq3
#eval Finite.beq (.arr .bool .bool) id (not ∘ not)
```
```anchorInfo arrBoolBoolEq3
true
```
{anchorName Finite}`Finite`宇宙がコード化しているのは、ライブラリが作った特別な類似物ではなく、Leanの*実際の*関数型だからである。
:::

{anchorName FiniteAll}`enumerate`の実装も、{anchorName FiniteAll}`Finite`のコードについての再帰によるものである。
```anchor FiniteAll
  def Finite.enumerate (t : Finite) : List t.asType :=
    match t with
    | .unit => [()]
    | .bool => [true, false]
    | .pair t1 t2 => t1.enumerate.product t2.enumerate
    | .arr dom cod => dom.functions cod.enumerate
```
{anchorName Finite}`Unit`の場合は、値が一つしかない。
{anchorName Finite}`Bool`の場合は、返す値が二つ（{anchorName sundries}`true`と{anchorName sundries}`false`）ある。
組の場合は、{anchorName FiniteAll}`t1`がコード化する型の値と、{anchorName FiniteAll}`t2`がコード化する型の値の直積になるべきである。
言い換えれば、{anchorName FiniteAll}`dom`のどの値も{anchorName FiniteAll}`cod`のどの値と組になるべきである。
補助関数{anchorName ListProduct}`List.product`は普通の再帰関数でも書けるが、ここでは恒等モナドで{kw}`for`を使って定義している。

```anchor ListProduct
def List.product (xs : List α) (ys : List β) : List (α × β) := Id.run do
  let mut out : List (α × β) := []
  for x in xs do
    for y in ys do
      out := (x, y) :: out
  pure out.reverse
```
最後に、関数の場合の{anchorName FiniteAll}`Finite.enumerate`は、目標とする戻り値のリストを引数に取る{anchorName FiniteFunctionSigStart}`Finite.functions`という補助関数に委ねる。

一般に、ある有限の型から結果の値の集まりへの関数をすべて生成するのは、関数の表を生成することと考えられる。
各関数は各入力に出力を割り当てるので、可能な引数が$`k`個あるとき、ある関数の表は$`k`行になる。
表の各行は$`n`個の可能な出力のどれでも選べるので、生成すべき関数は$`n ^ k`個ありうる。

ここでもまた、有限の型から値のリストへの関数の生成は、その有限の型を記述するコードについて再帰的である。
```anchor FiniteFunctionSigStart
def Finite.functions
    (t : Finite)
    (results : List α) : List (t.asType → α) :=
  match t with
```

{anchorName Finite}`Unit`からの関数の表は1行である。与えられた入力によって違う結果を選ぶことができないためである。
つまり、起こりうる入力ごとに関数が一つ生成される。
```anchor FiniteFunctionUnit
| .unit =>
  results.map fun r =>
    fun () => r
```
結果の値が$`n`個あるとき、{anchorName sundries}`Bool`からの関数は$`n^2`個ある。型{anchorTerm sundries}`Bool → α`の個々の関数は、{anchorName sundries}`Bool`を使って二つの特定の{anchorName sundries}`α`のどちらかを選ぶためである。
```anchor FiniteFunctionBool
| .bool =>
  (results.product results).map fun (r1, r2) =>
    fun
      | true => r1
      | false => r2
```
組からの関数の生成は、カリー化を利用して行える。
組からの関数は、組の最初の要素を取り、組の二番目の要素を待つ関数を返す関数に変換できる。
そうすれば、この場合に{anchorName FiniteFunctionSigStart}`Finite.functions`を再帰的に使える。
```anchor FiniteFunctionPair
| .pair t1 t2 =>
  let f1s := t1.functions <| t2.functions results
  f1s.map fun f =>
    fun (x, y) =>
      f x y
```

高階の関数の生成は少し頭がこんがらがる。
高階の関数はそれぞれ関数を引数に取る。
この引数の関数は、その入力と出力の振る舞いによって他の関数と区別できる。
一般に、高階の関数は引数の関数をありとあらゆる引数に適用でき、そのうえで引数の関数を適用した結果に基づいてありとあらゆる振る舞いを行える。
このことから、高階の関数を組み立てる手段が示唆される。
 * それ自体が引数である関数への、ありとあらゆる引数のリストから始める。
 * 起こりうる引数ごとに、その引数に引数の関数を適用して観察した結果から生じうる、ありとあらゆる振る舞いを組み立てる。これは{anchorName FiniteFunctionSigStart}`Finite.functions`と残りの引数についての再帰で行える。その再帰の結果が、残りの引数についての観察に基づく関数を表すためである。{anchorName FiniteFunctionSigStart}`Finite.functions`は、現在の引数についての観察に基づいてそれらを達成するありとあらゆる方法を組み立てる。
 * これらの観察に応じた起こりうる振る舞いごとに、引数の関数を現在の引数に適用する高階の関数を組み立てる。その結果が、その観察の振る舞いに渡される。
 * 再帰の基底の場合は、各結果の値について何も観察しない高階の関数である。引数の関数を無視して、単にその結果の値を返す。

この再帰関数を直接定義すると、Leanは関数全体の停止性を証明できなくなる。
しかし、*右畳み込み*と呼ばれるより単純な形の再帰を使えば、停止性の検査器に関数が停止すると明確に示せる。
右畳み込みは三つの引数を取る。リストの先頭と、残りについての再帰の結果を組み合わせる段階の関数、リストが空のときに返す既定の値、そして処理するリストである。
そしてリストを分析し、本質的にはリストの各{lit}`::`を段階の関数の呼び出しに置き換え、{lit}`[]`を既定の値に置き換える。

```anchor foldr
def List.foldr (f : α → β → β) (default : β) : List α → β
  | []     => default
  | a :: l => f a (foldr f default l)
```
リストにある{anchorName sundries}`Nat`の和を求めるのは{anchorName foldrSum}`foldr`で行える。
```anchorEvalSteps foldrSum
[1, 2, 3, 4, 5].foldr (· + ·) 0
===>
(1 :: 2 :: 3 :: 4 :: 5 :: []).foldr (· + ·) 0
===>
(1 + 2 + 3 + 4 + 5 + 0)
===>
15
```

{anchorName foldrSum}`foldr`を使うと、高階の関数は次のように作れる。
```anchor FiniteFunctionArr
    | .arr t1 t2 =>
      let args := t1.enumerate
      let base :=
        results.map fun r =>
          fun _ => r
      args.foldr
        (fun arg rest =>
          (t2.functions rest).map fun more =>
            fun f => more (f arg) f)
        base
```
{anchorName FiniteFunctions}`Finite.functions`の完全な定義は次のとおりである。
```anchor FiniteFunctions
def Finite.functions
    (t : Finite)
    (results : List α) : List (t.asType → α) :=
  match t with
| .unit =>
  results.map fun r =>
    fun () => r
| .bool =>
  (results.product results).map fun (r1, r2) =>
    fun
      | true => r1
      | false => r2
| .pair t1 t2 =>
  let f1s := t1.functions <| t2.functions results
  f1s.map fun f =>
    fun (x, y) =>
      f x y
    | .arr t1 t2 =>
      let args := t1.enumerate
      let base :=
        results.map fun r =>
          fun _ => r
      args.foldr
        (fun arg rest =>
          (t2.functions rest).map fun more =>
            fun f => more (f arg) f)
        base
```



{anchorName MutualStart}`Finite.enumerate`と{anchorName FiniteFunctions}`Finite.functions`は互いを呼び出すので、{kw}`mutual`ブロックの中で定義する必要がある。
言い換えれば、{anchorName MutualStart}`Finite.enumerate`の定義のすぐ前に{kw}`mutual`キーワードがある。
```anchor MutualStart
mutual
  def Finite.enumerate (t : Finite) : List t.asType :=
    match t with
```
また、{anchorName FiniteFunctions}`Finite.functions`の定義のすぐ後に{kw}`end`キーワードがある。
```anchor MutualEnd
    | .arr t1 t2 =>
      let args := t1.enumerate
      let base :=
        results.map fun r =>
          fun _ => r
      args.foldr
        (fun arg rest =>
          (t2.functions rest).map fun more =>
            fun f => more (f arg) f)
        base
end
```

この関数を比較する算法は、特に実用的というわけではない。
調べる場合の数は指数関数的に増える。{anchorTerm lots}`((Bool × Bool) → Bool) → Bool`のような単純な型でも、{anchorInfoText nestedFunLength}`65536`個の異なる関数を記述する。
なぜそんなに多いのか。
以上の推論に基づき、型$`T`が記述する値の数を$`\left| T \right|`で表すと、次のようになると予想される。
$$`\left| \left( \left( \mathtt{Bool} \times \mathtt{Bool} \right) \rightarrow \mathtt{Bool} \right) \rightarrow \mathtt{Bool} \right|`
は次のようになり、
$$`\left|\mathrm{Bool}\right|^{\left| \left( \mathtt{Bool} \times \mathtt{Bool} \right) \rightarrow \mathtt{Bool} \right| },`
これは次のようになり、
$$`2^{2^{\left| \mathtt{Bool} \times \mathtt{Bool} \right| }},`
これは次のようになり、
$$`2^{2^4}`
つまり65536である。
入れ子になった指数は速く増大し、高階の関数はたくさんある。


# 練習問題
%%%
tag := "universe-exercises"
%%%

 * {anchorName Finite}`Finite`がコード化する型のどの値でも文字列に変換する関数を書け。関数はその表として表すものとする。
 * 空の型{anchorName sundries}`Empty`を{anchorName Finite}`Finite`と{anchorName FiniteBeq}`Finite.beq`に加えよ。
 * {anchorName sundries}`Option`を{anchorName Finite}`Finite`と{anchorName FiniteBeq}`Finite.beq`に加えよ。
