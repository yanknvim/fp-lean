module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

example_module Examples.Intro

set_option verso.exampleProject "../examples"

set_option verso.exampleModule "Examples.Intro"

#doc (Manual) "Polymorphism" =>
%%%
tag := "polymorphism"
%%%

ほとんどの言語と同じく、Leanの型も引数を取れる。
たとえば{anchorTerm fragments}`List Nat`は自然数のリストを、{anchorTerm fragments}`List String`は文字列のリストを、{anchorTerm fragments}`List (List Point)`は点のリストのリストを表す。
これは、C#やJavaのような言語の{CSharp}`List<Nat>`、{CSharp}`List<String>`、{CSharp}`List<List<Point>>`とよく似ている。
Leanが関数に引数を渡すのに空白を使うのと同じように、型に引数を渡すのにも空白を使う。

関数型プログラミングでは、*多相性*という語は通常、型を引数に取るデータ型や定義を指す。
オブジェクト指向プログラミングの世界では、この語は通常、スーパークラスの振る舞いを上書きできるサブクラスを指すので、意味が異なる。
本書では、「多相性」は常に前者の意味で使う。
型引数はデータ型や定義の中で使える。引数の名前を別の型で置き換えて得られるどの型に対しても、同じデータ型や定義を使えるようになる。

:::paragraph
{anchorName Point}`Point`構造体は、{anchorName Point}`x`と{anchorName Point}`y`の両方のフィールドが{anchorName Point}`Float`であることを要求する。
しかし、点だからといって各座標の表現を特定しなければならない理由はない。
{anchorName Point}`Point`を多相にした{anchorName PPoint}`PPoint`は、型を引数に取り、その型を両方のフィールドに使える。

```anchor PPoint
structure PPoint (α : Type) where
  x : α
  y : α
```

:::

関数定義の引数が定義する名前の直後に書かれるのと同じように、構造体の引数は構造体の名前の直後に書く。
Leanでは、これといった名前が思いつかないときは、型引数にギリシャ文字を使うのが慣例である。
{anchorTerm PPoint}`Type`は他の型を記述する型なので、{anchorName Nat}`Nat`、{anchorTerm fragments}`List String`、{anchorTerm fragments}`PPoint Int`はいずれも{anchorTerm PPoint}`Type`という型を持つ。

:::paragraph
{anchorName fragments}`List`と同じく、{anchorName PPoint}`PPoint`は具体的な型を引数として渡して使える。

```anchor natPoint
def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }
```

この例では、両方のフィールドが{anchorName natPoint}`Nat`であることが期待される。
関数が引数の変数を引数の値で置き換えて呼び出されるのと同じように、{anchorName PPoint}`PPoint`に{anchorName fragments}`Nat`という型を引数として渡すと、フィールド{anchorName PPoint}`x`と{anchorName PPoint}`y`が{anchorName fragments}`Nat`型の構造体が得られる。引数の名前{anchorName PPoint}`α`が引数の型{anchorName fragments}`Nat`で置き換えられるためである。
Leanでは型も普通の式なので、{anchorName PPoint}`PPoint`のような多相型に引数を渡すのに特別な記法は要らない。
:::

:::paragraph
定義も型を引数に取ることができ、そうすると多相になる。
関数{anchorName replaceX}`replaceX`は、{anchorName replaceX}`PPoint`の{anchorName replaceX}`x`フィールドを新しい値に置き換える。
{anchorName replaceX}`replaceX`を*任意の*多相的な点に対して使えるようにするには、この関数自身も多相でなければならない。
そのためには、最初の引数を点のフィールドの型にし、後ろの引数がその引数の名前を参照する形にすればよい。

```anchor replaceX
def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }
```

言い換えれば、引数{anchorName replaceX}`point`と{anchorName replaceX}`newX`の型に{anchorName replaceX}`α`が現れるとき、それは*最初の引数として渡された型*を指している。
これは、関数の本体に現れる引数の名前が、渡された値を指すのと似ている。
:::

:::paragraph

Leanに{anchorName replaceX}`replaceX`の型を調べさせ、次に{anchorTerm replaceXNatOriginFiveT}`replaceX Nat`の型を調べさせると、これが分かる。

```anchorTerm replaceXT
#check (replaceX)
```

```anchorInfo replaceXT
replaceX : (α : Type) → PPoint α → α → PPoint α
```

この関数の型には最初の引数の*名前*が含まれており、型の中の後ろの引数がその名前を参照している。
関数適用の値が、関数の本体で引数の名前を渡された値で置き換えて求められるのと同じように、関数適用の型は、戻り値の型で引数の名前を渡された値で置き換えて求められる。
最初の引数として{anchorName replaceXNatT}`Nat`を渡すと、型の残りの部分にある{anchorName replaceX}`α`がすべて{anchorName replaceXNatT}`Nat`で置き換わる。

```anchorTerm replaceXNatT
#check replaceX Nat
```

```anchorInfo replaceXNatT
replaceX Nat : PPoint Nat → Nat → PPoint Nat
```

残りの引数には名前が付いていないので、引数をさらに渡しても置き換えは起こらない。

```anchorTerm replaceXNatOriginT
#check replaceX Nat natOrigin
```

```anchorInfo replaceXNatOriginT
replaceX Nat natOrigin : Nat → PPoint Nat
```

```anchorTerm replaceXNatOriginFiveT
#check replaceX Nat natOrigin 5
```

```anchorInfo replaceXNatOriginFiveT
replaceX Nat natOrigin 5 : PPoint Nat
```

:::

:::paragraph
型を引数として渡すことで式全体の型が決まるからといって、その式を評価できるかどうかには関係がない。

```anchorTerm replaceXNatOriginFiveV
#eval replaceX Nat natOrigin 5
```

```anchorInfo replaceXNatOriginFiveV
{ x := 5, y := 0 }
```

:::

:::paragraph
多相関数は、名前付きの型引数を取り、後ろの型がその引数の名前を参照する形で成り立っている。
ただし、名前を付けられるのは型引数に限った話ではない。
正負の符号を表すデータ型を考える。

```anchor Sign
inductive Sign where
  | pos
  | neg
```

:::

:::paragraph
符号を引数に取る関数を書くことができる。
引数が正なら{anchorName posOrNegThree}`Nat`を、負なら{anchorName posOrNegThree}`Int`を返すようにできる。

```anchor posOrNegThree
def posOrNegThree (s : Sign) :
    match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)
```

型は第一級であり、Leanの言語の普通の規則で計算できるので、データ型に対するパターンマッチングで型を計算できる。
Leanがこの関数を検査するとき、関数の本体の{kw}`match`式と型の{kw}`match`式が対応していることを利用して、{anchorName Sign}`pos`の場合の期待される型を{anchorName posOrNegThree}`Nat`に、{anchorName Sign}`neg`の場合の期待される型を{anchorName posOrNegThree}`Int`にする。

:::

:::paragraph
{anchorName posOrNegThree}`posOrNegThree`を{anchorName Sign}`pos`に適用すると、関数の本体と戻り値の型の両方で、引数名{anchorName posOrNegThree}`s`が{anchorName Sign}`pos`で置き換えられる。
評価は式でもその型でも起こる。

```anchorEvalSteps posOrNegThreePos
(posOrNegThree Sign.pos :
 match Sign.pos with | Sign.pos => Nat | Sign.neg => Int)
===>
((match Sign.pos with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)) :
 match Sign.pos with | Sign.pos => Nat | Sign.neg => Int)
===>
((3 : Nat) : Nat)
===>
3
```

:::

# 連結リスト
%%%
tag := "linked-lists"
%%%

:::paragraph
Leanの標準ライブラリには{anchorName fragments}`List`という標準的な連結リストのデータ型と、それを使いやすくする特別な記法がある。
リストは角括弧で書く。
たとえば、10未満の素数を入れたリストは次のように書ける。

```anchor primesUnder10
def primesUnder10 : List Nat := [2, 3, 5, 7]
```

:::

:::paragraph
舞台裏では、{anchorName List}`List`は次のように定義された帰納的データ型である。

```anchor List
inductive List (α : Type) where
  | nil : List α
  | cons : α → List α → List α
```

標準ライブラリでの実際の定義は、まだ説明していない機能を使っているため少し異なるが、ほぼ同じである。
この定義は、{anchorName PPoint}`PPoint`と同じく、{anchorName List}`List`が型を一つ引数に取ることを示している。
この型が、リストに入れる要素の型である。
コンストラクタによれば、{anchorTerm List}`List α`は{anchorName List}`nil`か{anchorName List}`cons`で作れる。
コンストラクタ{anchorName List}`nil`は空のリストを表し、{anchorName List}`cons`は空でないリストに使う。
{anchorName List}`cons`の最初の引数がリストの先頭、二番目の引数が残りである。
$`n`個の要素を持つリストには$`n`個の{anchorName List}`cons`コンストラクタが入り、最後のものの残りは{anchorName List}`nil`である。

:::

:::paragraph
{anchorName primesUnder10}`primesUnder10`の例は、{anchorName List}`List`のコンストラクタを直接使ってより明示的に書ける。

```anchor explicitPrimesUnder10
def explicitPrimesUnder10 : List Nat :=
  List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))
```

この二つの定義は完全に同等だが、{anchorName primesUnder10}`primesUnder10`の方が{anchorName explicitPrimesUnder10}`explicitPrimesUnder10`よりずっと読みやすい。
:::

:::paragraph
{anchorName List}`List`を消費する関数は、{anchorName Nat}`Nat`を消費する関数とほぼ同じように定義できる。
実際、連結リストは、各{anchorName Nat}`succ`コンストラクタにデータのフィールドがぶら下がった{anchorName Nat}`Nat`だと考えることもできる。
この見方では、リストの長さを求めるのは、各{anchorName List}`cons`を{anchorName Nat}`succ`に、最後の{anchorName List}`nil`を{anchorName Nat}`zero`に置き換えていく作業である。
{anchorName replaceX}`replaceX`が点のフィールドの型を引数に取ったのと同じように、{anchorName length1EvalSummary}`length`はリストの要素の型を引数に取る。
たとえば、リストが文字列を入れるものなら、最初の引数は{anchorName length1EvalSummary}`String`であり、{anchorEvalStep length1EvalSummary 0}`length String ["Sourdough", "bread"]`となる。
これは次のように計算されるはずである。

```anchorEvalSteps length1EvalSummary
length String ["Sourdough", "bread"]
===>
length String (List.cons "Sourdough" (List.cons "bread" List.nil))
===>
Nat.succ (length String (List.cons "bread" List.nil))
===>
Nat.succ (Nat.succ (length String List.nil))
===>
Nat.succ (Nat.succ Nat.zero)
===>
2
```

:::

:::paragraph

{anchorName length1}`length`の定義は、多相であり（リストの要素の型を引数に取るため）、かつ再帰的である（自分自身を参照するため）。
一般に、関数はデータの形に沿う。再帰的なデータ型からは再帰関数が、多相的なデータ型からは多相関数が生まれる。

```anchor length1
def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons y ys => Nat.succ (length α ys)
```

:::

{lit}`xs`や{lit}`ys`のような名前は、値が不明なリストを表すのに慣例的に使う。
名前の{lit}`s`は複数であることを示すので、「エックス」ではなく「エックシズ」、「ワイ」ではなく「ワイズ」と読む。

:::paragraph
リストを扱う関数を読みやすくするため、{anchorName List}`nil`に対するパターンマッチングには角括弧の記法{anchorTerm length2}`[]`を、{anchorName List}`cons`の代わりには中置の{anchorTerm length2}`::`を使える。

```anchor length2
def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length α ys)
```

:::

# 暗瞑の引数
%%%
tag := "implicit-parameters"
%%%

:::paragraph
{anchorName replaceX}`replaceX`と{anchorName length1}`length`はどちらも、使うときに引数が煩わしい。型引数は通常、後ろの値から一意に決まるためである。
実際、ほとんどの言語では、コンパイラが型引数を自分で決められ、利用者の助けが必要になるのはごくたまである。
Leanでも同じである。
関数を定義するとき、引数を括弧ではなく淡括弧で囲むと、その引数を*暗瞑*にできる。
たとえば、型引数を暗瞑にした{anchorName replaceXImp}`replaceX`は次のようになる。

```anchor replaceXImp
def replaceX {α : Type} (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }
```

{anchorName replaceXImpNat}`natOrigin`に対しては、{anchorName NatDoubleFour}`Nat`を明示しなくても使える。Leanが後ろの引数から{anchorName replaceXImp}`α`の値を*推論*できるためである。

```anchor replaceXImpNat
#eval replaceX natOrigin 5
```

```anchorInfo replaceXImpNat
{ x := 5, y := 0 }
```

:::

:::paragraph

同様に、{anchorName lengthImp}`length`も要素の型を暗瞑に取るように定義し直せる。

```anchor lengthImp
def length {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length ys)
```

この{anchorName lengthImp}`length`は{anchorName lengthImpPrimes}`primesUnder10`に直接適用できる。

```anchor lengthImpPrimes
#eval length primesUnder10
```

```anchorInfo lengthImpPrimes
4
```

:::

:::paragraph
標準ライブラリでは、この関数は{anchorName lengthExpNat}`List.length`という名前である。そのため、構造体のフィールドにアクセスするドット記法を、リストの長さを求めるのにも使える。

```anchor lengthDotPrimes
#eval primesUnder10.length
```

```anchorInfo lengthDotPrimes
4
```

:::

:::paragraph
C#やJavaでも型引数を明示しなければならないことがあるように、Leanも常に暗瞑の引数を見つけられるわけではない。
そのような場合は、名前を使って指定できる。
たとえば、整数のリストにだけ使える{anchorName lengthExpNat}`List.length`は、{anchorTerm lengthExpNat}`α`を{anchorName lengthExpNat}`Int`に設定して指定できる。

```anchor lengthExpNat
#check List.length (α := Int)
```

```anchorInfo lengthExpNat
List.length : List Int → Nat
```

:::

# その他の組み込みデータ型
%%%
tag := "more-built-in-types"
%%%

リストのほかにも、Leanの標準ライブラリには、さまざまな場面で使える構造体と帰納的データ型が多数ある。

## {lit}`Option`
%%%
tag := "Option"
%%%
すべてのリストに先頭の要素があるわけではない。空のリストもある。
コレクションに対する操作の多くは、探しているものが見つからないことがある。
たとえば、リストの先頭の要素を求める関数は、そのような要素が見つからないことがある。
そのため、先頭の要素がなかったことを伝える手段が必要になる。

多くの言語には、値が存在しないことを表す{CSharp}`null`という値がある。
Leanは、既存の型に特別な{CSharp}`null`値を付けるのではなく、別の型に値の欠如を示す印を付ける{anchorName Option}`Option`というデータ型を用意している。
たとえば、nullになりうる{anchorName fragments}`Int`は{anchorTerm nullOne}`Option Int`で、nullになりうる文字列のリストは{anchorTerm fragments}`Option (List String)`で表す。
nullになりうることを表すのに新しい型を導入すると、{CSharp}`null`の確認を忘れられなくなることを型システムが保証する。{anchorName nullOne}`Int`が期待される場所では{anchorTerm nullOne}`Option Int`を使えないためである。

:::paragraph
{anchorName Option}`Option`には{anchorName Option}`some`と{anchorName Option}`none`の二つのコンストラクタがあり、それぞれ元の型の値がある場合とない場合を表す。
値がある場合のコンストラクタ{anchorName Option}`some`は元の値を入れ、{anchorName Option}`none`は引数を取らない。

```anchor Option
inductive Option (α : Type) : Type where
  | none : Option α
  | some (val : α) : Option α
```

:::

{anchorName Option}`Option`型は、C#やKotlinのような言語のnull許容型とよく似ているが、同じではない。
これらの言語では、ある型（たとえば{CSharp}`Boolean`）が常にその型の実際の値（{CSharp}`true`と{CSharp}`false`）を指すのに対し、{CSharp}`Boolean?`や{CSharp}`Nullable<Boolean>`という型は{CSharp}`null`値も許す。
これを型システムで追跡できるのは非常に役に立つ。型チェッカや他のツールが{CSharp}`null`の確認を忘れないよう助けてくれるし、型シグネチャでnullになりうることを明示したAPIは、そうでないAPIより情報量が多い。
ただし、こうしたnull許容型は、Leanの{anchorName Option}`Option`と決定的に異なる点が一つある。値がないかもしれないという状態を何層にも重ねられないのである。
{anchorTerm nullThree}`Option (Option Int)`は、{anchorTerm nullOne}`none`、{anchorTerm nullTwo}`some none`、{anchorTerm nullThree}`some (some 360)`のいずれでも作れる。
一方Kotlinでは、{Kotlin}`T??`は{Kotlin}`T?`と同じものとして扱われる。
この微妙な違いが実際に問題になることはめったにないが、時には重要になる。

:::paragraph
リストの先頭の要素があるならそれを求めるには、{anchorName headHuh}`List.head?`を使う。
疑問符は名前の一部であり、C#やKotlinでnull許容型を表す疑問符とは関係がない。
{anchorName headHuh}`List.head?`の定義では、リストの残りをアンダースコアで表している。
パターンにおいて、アンダースコアは何にでも一致するが、一致したデータを指す変数は導入しない。
名前の代わりにアンダースコアを使うのは、入力の一部を無視していることを読み手にはっきり伝える方法である。

```anchor headHuh
def List.head? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | y :: _ => some y
```

:::

Leanの命名の慣例では、失敗しうる操作をまとめて定義するとき、{anchorName Option}`Option`を返す版には{lit}`?`、不正な入力でクラッシュする版には{lit}`!`、失敗する代わりに既定値を返す版には{lit}`D`という接尾辞を付ける。
この慣例に従うと、{anchorName fragments}`List.head`はリストが空でないという数学的な証拠を呼び出し側に要求し、{anchorName fragments}`List.head?`は{anchorName Option}`Option`を返し、{anchorName fragments}`List.head!`は空のリストを渡されるとプログラムをクラッシュさせ、{anchorName fragments}`List.headD`はリストが空の場合に返す既定値を受け取る。
疑問符と感嘆符は特別な構文ではなく名前の一部である。Leanの命名規則は多くの言語より自由だからである。

:::paragraph

{anchorName fragments}`head?`は{lit}`List`名前空間で定義されているので、アクセサ記法で使える。

```anchor headSome
#eval primesUnder10.head?
```

```anchorInfo headSome
some 2
```

ただし、空のリストに対して試すと二つのエラーになる。

```anchor headNoneBad
#eval [].head?
```

```anchorError headNoneBad
don't know how to synthesize implicit argument `α`
  @List.nil ?m.3
context:
⊢ Type ?u.71462
```

```anchorError headNoneBad
don't know how to synthesize implicit argument `α`
  @_root_.List.head? ?m.3 []
context:
⊢ Type ?u.71462
```

:::

:::paragraph
これは、Leanが式の型を完全には決められなかったためである。
とくに、{anchorName fragments}`List.head?`の暗瞑の型引数も、{anchorName fragments}`List.nil`の暗瞑の型引数も見つけられなかった。
Leanの出力で{lit}`?m.XYZ`は、推論できなかった部分を表す。
このような未知の部分を*メタ変数*と呼び、いくつかのエラーメッセージに現れる。
式を評価するにはLeanがその型を求められる必要があるが、空のリストには型を決める手がかりになる要素がないため、型が分からなかった。
型を明示すれば、Leanは先に進める。

```anchor headNone
#eval [].head? (α := Int)
```

```anchorInfo headNone
none
```

型は型注釈でも指定できる。

```anchor headNoneTwo
#eval ([] : List Int).head?
```

```anchorInfo headNoneTwo
none
```

このエラーメッセージには役に立つ手がかりがある。
どちらのメッセージも、欠けている暗瞑の引数を*同じ*メタ変数で表している。つまりLeanは、足りない二つの部分が同じ答えを共有することは突き止めたが、その答えの実際の値までは決められなかったのである。

:::

## {lit}`Prod`
%%%
tag := "prod"
%%%

{anchorName Prod}`Prod`構造体は「Product」の略で、二つの値を一組にする一般的な方法である。
たとえば{anchorTerm fragments}`Prod Nat String`は{anchorName fragments}`Nat`と{anchorName fragments}`String`を入れる。
言い換えれば、{anchorTerm natPoint}`PPoint Nat`は{anchorTerm fragments}`Prod Nat Nat`で置き換えられる。
{anchorName fragments}`Prod`は、C#のタプル、Kotlinの{Kotlin}`Pair`と{Kotlin}`Triple`、C++の{cpp}`tuple`とよく似ている。
アプリケーションの多くは、{anchorName Point}`Point`のような簡単な場合でも独自の構造体を定義する方がよい。その分野の用語を使うとコードが読みやすくなるためである。
さらに、構造体型を定義すると、分野の概念ごとに異なる型を割り当てて取り違えを防げるので、誤りを見つけやすくなる。

一方で、新しい型を定義する手間に見合わない場合もある。
また、ライブラリによっては十分に一般的で、「組」より具体的な概念が存在しないこともある。
さらに、標準ライブラリには、組み込みの組の型を扱いやすくする便利な関数がいろいろある。

:::paragraph
構造体{anchorName Prod}`Prod`は二つの型引数を持って定義されている。

```anchor Prod
structure Prod (α : Type) (β : Type) : Type where
  fst : α
  snd : β
```

:::

:::paragraph
リストは非常によく使うので、読みやすくするための特別な記法がある。
同じ理由で、直積型とそのコンストラクタにも特別な記法がある。
型{anchorTerm ProdSugar}`Prod α β`は通常{anchorTerm ProdSugar}`α × β`と書く。集合の直積の普通の記法にならったものである。
同様に、{anchorName ProdSugar}`Prod`には数学で普通に使う組の記法も用意されている。
つまり、次のように書く代わりに、

```anchor fivesStruct
def fives : String × Int := { fst := "five", snd := 5 }
```

次のように書けばよい。

```anchor fives
def fives : String × Int := ("five", 5)
```

:::

:::paragraph

どちらの記法も右結合である。
つまり、次の二つの定義は同じ意味である。

```anchor sevens
def sevens : String × Int × Nat := ("VII", 7, 4 + 3)
```

```anchor sevensNested
def sevens : String × (Int × Nat) := ("VII", (7, 4 + 3))
```

言い換えれば、三つ以上の型の直積とそれに対応するコンストラクタは、舞台裏では入れ子になった直積と組になっている。

:::


## {anchorName Sum}`Sum`
%%%
tag := "Sum"
%%%

{anchorName Sum}`Sum`データ型は、異なる二つの型の値のどちらかを選べるようにする一般的な方法である。
たとえば{anchorTerm fragments}`Sum String Int`は、{anchorName fragments}`String`か{anchorName fragments}`Int`のどちらかである。
{anchorName Prod}`Prod`と同じく、{anchorName Sum}`Sum`は、非常に一般的なコードを書くとき、分野固有の適切な型がないごく小さな部分に使うとき、あるいは標準ライブラリに役立つ関数がそろっているときに使う。
ほとんどの場面では、独自の帰納型を使う方が読みやすく保守しやすい。

:::paragraph
{anchorTerm Sumαβ}`Sum α β`型の値は、{anchorName Sum}`α`型の値にコンストラクタ{anchorName Sum}`inl`を適用したものか、{anchorName Sum}`β`型の値にコンストラクタ{anchorName Sum}`inr`を適用したものである。

```anchor Sum
inductive Sum (α : Type) (β : Type) : Type where
  | inl : α → Sum α β
  | inr : β → Sum α β
```

これらの名前は、それぞれ「左入射」「右入射」の略である。
{anchorName Prod}`Prod`に直積の記法を使うのと同じように、{anchorName SumSugar}`Sum`には「丸付きプラス」の記法を使うので、{anchorTerm SumSugar}`α ⊕ β`は{anchorTerm SumSugar}`Sum α β`の別の書き方である。
{anchorName FakeSum}`Sum.inl`と{anchorName FakeSum}`Sum.inr`には特別な記法はない。

:::

:::paragraph
例として、ペットの名前が犬の名前か猫の名前のどちらかだとすると、その型は文字列の直和として導入できる。

```anchor PetName
def PetName : Type := String ⊕ String
```

実際のプログラムでは、たいてい、意味の分かるコンストラクタ名を持つ独自の帰納型を定義した方がよい。
ここでは、犬の名前に{anchorName animals}`Sum.inl`を、猫の名前に{anchorName animals}`Sum.inr`を使うことにする。
これらのコンストラクタを使って、動物の名前のリストを書ける。

```anchor animals
def animals : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi",
   Sum.inl "Rex", Sum.inr "Floof"]
```

:::

:::paragraph
二つのコンストラクタの区別にはパターンマッチングを使える。
たとえば、動物の名前のリストに犬が何匹いるか（つまり{anchorName howManyDogs}`Sum.inl`コンストラクタの個数）を数える関数は次のようになる。

```anchor howManyDogs
def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets
```

関数呼び出しは中置演算子より先に評価されるので、{anchorTerm howManyDogsAdd}`howManyDogs morePets + 1`は{anchorTerm howManyDogsAdd}`(howManyDogs morePets) + 1`と同じである。
期待どおり、{anchor dogCount}`#eval howManyDogs animals`は{anchorInfo dogCount}`3`になる。
:::

## {anchorName Unit}`Unit`
%%%
tag := "Unit"
%%%

:::paragraph
{anchorName Unit}`Unit`は、引数を取らないコンストラクタ{anchorName Unit}`unit`を一つだけ持つ型である。
言い換えれば、そのコンストラクタを一切の引数なしに適用した、ただ一つの値だけを表す。
{anchorName Unit}`Unit`は次のように定義される。

```anchor Unit
inductive Unit : Type where
  | unit : Unit
```

:::

:::paragraph
{anchorName Unit}`Unit`それ自体は、あまり役に立たない。
しかし多相的なコードでは、欠けているデータの場所を埋めるのに使える。
たとえば、次の帰納的データ型は算術式を表す。

```anchor ArithExpr
inductive ArithExpr (ann : Type) : Type where
  | int : ann → Int → ArithExpr ann
  | plus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | minus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | times : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
```

型引数{anchorName ArithExpr}`ann`は注釈を表し、どのコンストラクタにも注釈が付く。
パーサから得た式にはソース上の位置を注釈として付けられるので、戻り値の型を{anchorTerm ArithExprEx}`ArithExpr SourcePos`にしておけば、パーサが各部分式に{anchorName ArithExprEx}`SourcePos`を付けたことが保証される。
一方、パーサから来ない式にはソース上の位置がないので、その型は{anchorTerm ArithExprEx}`ArithExpr Unit`でよい。

:::

さらに、Leanの関数はすべて引数を持つので、他の言語の引数なしの関数は、{anchorName ArithExprEx}`Unit`の引数を取る関数として表せる。
戻り値の位置では、{anchorName ArithExprEx}`Unit`型はC系の言語の{CSharp}`void`に似ている。
C系の言語では、{CSharp}`void`を返す関数は呼び出し元に制御を返すが、意味のある値は返さない。
{anchorName ArithExprEx}`Unit`は意図的に意味のない値であることで、型システムに{CSharp}`void`専用の機能を用意しなくてもこれを表せるようにする。
Unitのコンストラクタは空の括弧で書ける。{anchorTerm unitParens}`() : Unit`である。

## {lit}`Empty`
%%%
tag := "Empty"
%%%

{anchorName fragments}`Empty`データ型にはコンストラクタが一つもない。
したがって、到達しないコードを表す。{anchorName fragments}`Empty`型の値で終わる呼び出しの連なりは存在しないためである。

{anchorName fragments}`Empty`は、{anchorName fragments}`Unit`ほど頻繁には使わない。
しかし、特殊な場面では役に立つ。
多相的なデータ型の多くは、すべてのコンストラクタで型引数をすべて使うわけではない。
たとえば{anchorName animals}`Sum.inl`と{anchorName animals}`Sum.inr`は、それぞれ{anchorName fragments}`Sum`の型引数のうち一つしか使わない。
{anchorName fragments}`Sum`の型引数の一つに{anchorName fragments}`Empty`を使うと、プログラムのある地点でコンストラクタの一方を排除できる。
これにより、追加の制約がある場面でも一般的なコードを使えるようになる。

## 直和型、直積型、Unitという名前
%%%
tag := "sum-products-units"
%%%

一般に、複数のコンストラクタを提供する型を*直和型*、一つのコンストラクタが複数の引数を取る型を{deftech}*直積型*と呼ぶ。
これらの用語は、普通の算数で使う和と積に関係がある。
この関係は、対象の型が有限個の値しか持たないときに最も分かりやすい。
{anchorName SumProd}`α`と{anchorName SumProd}`β`がそれぞれ$`n`個と$`k`個の異なる値を持つ型なら、{anchorTerm SumProd}`α ⊕ β`は$`n + k`個、{anchorTerm SumProd}`α × β`は$`n \times k`個の異なる値を持つ。
たとえば{anchorName fragments}`Bool`には{anchorName BoolNames}`true`と{anchorName BoolNames}`false`の二つの値があり、{anchorName Unit}`Unit`には{anchorName BooloUnit}`Unit.unit`という一つの値がある。
直積{anchorTerm fragments}`Bool × Unit`には{anchorTerm BoolxUnit}`(true, Unit.unit)`と{anchorTerm BoolxUnit}`(false, Unit.unit)`の二つの値があり、直和{anchorTerm fragments}`Bool ⊕ Unit`には{anchorTerm BooloUnit}`Sum.inl true`、{anchorTerm BooloUnit}`Sum.inl false`、{anchorTerm BooloUnit}`Sum.inr Unit.unit`の三つの値がある。
同様に$`2 \times 1 = 2`であり、$`2 + 1 = 3`である。

# 出会うかもしれないメッセージ
%%%
tag := "polymorphism-messages"
%%%

:::paragraph
定義できる構造体や帰納型が、すべて{anchorTerm Prod}`Type`という型を持てるわけではない。
とくに、コンストラクタが任意の型を引数に取る場合、その帰納型は別の型を持たなければならない。
こうしたエラーは通常、「宇宙レベル」に関することを述べている。
たとえば、次の帰納型を考える。

```anchor TypeInType
inductive MyType : Type where
  | ctor : (α : Type) → α → MyType
```

Leanは次のエラーを出す。

```anchorError TypeInType
Invalid universe level in constructor `MyType.ctor`: Parameter `α` has type
  Type
at universe level
  2
which is not less than or equal to the inductive type's resulting universe level
  1
```

なぜこうなるのか、また定義をどう直せば通るのかは、後の章で説明する。
今のところは、型をコンストラクタではなく帰納型全体の引数にしてみるとよい。
:::

:::paragraph
同様に、コンストラクタの引数が、定義しようとしているデータ型を引数に取る関数である場合、その定義は受け入れられない。
たとえば、

```anchor Positivity
inductive MyType : Type where
  | ctor : (MyType → Int) → MyType
```

とすると、次のメッセージが出る。

```anchorError Positivity
(kernel) arg #1 of 'MyType.ctor' has a non positive occurrence of the datatypes being declared
```

技術的な理由により、このようなデータ型を許すとLeanの内部論理が崩れ、定理証明器として使えなくなるおそれがある。
:::

:::paragraph
二つの引数を取る再帰関数では、その組に対してマッチさせるのではなく、各引数を別々にマッチさせる。
そうしないと、再帰呼び出しがより小さい値に対して行われるかを調べるLeanの仕組みが、入力の値と再帰呼び出しの引数のつながりを見いだせない。
たとえば、二つのリストの長さが等しいかを調べる次の関数は受け入れられない。

```anchor sameLengthPair
def sameLength (xs : List α) (ys : List β) : Bool :=
  match (xs, ys) with
  | ([], []) => true
  | (x :: xs', y :: ys') => sameLength xs' ys'
  | _ => false
```

エラーメッセージは次のとおりである。

```anchorError sameLengthPair
fail to show termination for
  sameLength
with errors
failed to infer structural recursion:
Not considering parameter α of sameLength:
  it is unchanged in the recursive calls
Not considering parameter β of sameLength:
  it is unchanged in the recursive calls
Cannot use parameter xs:
  failed to eliminate recursive application
    sameLength xs' ys'
Cannot use parameter ys:
  failed to eliminate recursive application
    sameLength xs' ys'


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
              xs ys
1) 1760:28-46  ?  ?
Please use `termination_by` to specify a decreasing measure.
```

この問題は、入れ子にしたパターンマッチングで解決できる。

```anchor sameLengthOk1
def sameLength (xs : List α) (ys : List β) : Bool :=
  match xs with
  | [] =>
    match ys with
    | [] => true
    | _ => false
  | x :: xs' =>
    match ys with
    | y :: ys' => sameLength xs' ys'
    | _ => false
```

次の節で説明する{ref "simultaneous-matching"}[同時マッチング]も、この問題を解く別の方法であり、しばしばより簡潔である。
:::

:::paragraph
帰納型の引数を忘れると、これも紛らわしいメッセージになる。
たとえば、{anchorTerm MissingTypeArg}`ctor`の型で{anchorName MissingTypeArg}`MyType`に引数{anchorName MissingTypeArg}`α`を渡し忘れると、次のようになる。

```anchor MissingTypeArg
inductive MyType (α : Type) : Type where
  | ctor : α → MyType
```

Leanは次のエラーを返す。

```anchorError MissingTypeArg
type expected, got
  (MyType : Type → Type)
```

このエラーメッセージは、{anchorName MissingTypeArg}`MyType`の型である{anchorTerm MissingTypeArgT}`Type → Type`が、それ自体は型を記述するものではない、と言っている。
{anchorName MissingTypeArg}`MyType`は、本当の型になるには引数が必要である。

:::

:::paragraph
同じメッセージは、定義の型シグネチャなど、別の場面で型引数を省略したときにも現れる。

```anchor MyTypeDef
inductive MyType (α : Type) : Type where
  | ctor : α → MyType α
```

```anchor MissingTypeArg2
def ofFive : MyType := ctor 5
```

```anchorError MissingTypeArg2
type expected, got
  (MyType : Type → Type)
```

:::

:::paragraph
多相型を使った式を評価すると、Leanが値を表示できない状況に陷ることがある。
{anchorTerm evalAxe}`#eval`コマンドは与えられた式を評価し、その式の型を使って結果の表示方法を決める。
関数のようないくつかの型ではこの処理が失敗するが、他のほとんどの型についてはLeanが表示用のコードを自動で生成できる。
たとえば{anchorName WoodSplittingTool}`WoodSplittingTool`に、表示用のコードを用意する必要はない。
```anchor WoodSplittingTool
inductive WoodSplittingTool where
  | axe
  | maul
  | froe
```
```anchor evalAxe
#eval WoodSplittingTool.axe
```
```anchorInfo evalAxe
WoodSplittingTool.axe
```
ただし、ここでLeanが行う自動化には限界がある。
{anchorName allTools}`allTools`は三つの道具をすべて入れたリストである。
```anchor allTools
def allTools : List WoodSplittingTool := [
  WoodSplittingTool.axe,
  WoodSplittingTool.maul,
  WoodSplittingTool.froe
]
```
これを評価するとエラーになる。
```anchor evalAllTools
#eval allTools
```
```anchorError evalAllTools
Could not synthesize a `ToExpr`, `Repr`, or `ToString` instance for type
  List WoodSplittingTool
```
Leanはリストを表示するのに組み込みの表にあるコードを使おうとするが、そのコードは{anchorName WoodSplittingTool}`WoodSplittingTool`の表示用コードがすでにあることを要求するためである。
このエラーは、{anchorTerm evalAllTools}`#eval`の時点で慌てて生成するのではなく、データ型を定義するときに表示用コードを生成するようLeanに指示すれば避けられる。定義に{anchorTerm Firewood}`deriving Repr`を加えればよい。
```anchor Firewood
inductive Firewood where
  | birch
  | pine
  | beech
deriving Repr
```
{anchorName Firewood}`Firewood`のリストの評価は成功する。
```anchor allFirewood
def allFirewood : List Firewood := [
  Firewood.birch,
  Firewood.pine,
  Firewood.beech
]
```
```anchor evalAllFirewood
#eval allFirewood
```
```anchorInfo evalAllFirewood
[Firewood.birch, Firewood.pine, Firewood.beech]
```
:::

# 練習問題
%%%
tag := "polymorphism-exercises"
%%%

 * リストの最後の要素を求める関数を書け。{anchorName fragments}`Option`を返すようにする。
 * 与えられた述語を満たす最初の要素をリストから求める関数を書け。定義は{anchorTerm List.findFirst?Ex}`def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α := …`から始める。
 * 組の二つのフィールドを入れ替える関数{anchorName Prod.switchEx}`Prod.switch`を書け。定義は{anchor Prod.switchEx}`def Prod.switch {α β : Type} (pair : α × β) : β × α := …`から始める。
 * {anchorName PetName}`PetName`の例を独自のデータ型を使う形に書き直し、{anchorName Sum}`Sum`を使った版と比べよ。
 * 二つのリストを組のリストにまとめる関数{anchorName zipEx}`zip`を書け。結果のリストの長さは、短い方の入力リストと同じにする。定義は{anchor zipEx}`def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) := …`から始める。
 * リストの先頭から$`n`個の要素を返す多相関数{anchorName takeOne}`take`を書け。$`n`は{anchorName fragments}`Nat`である。リストの要素が$`n`個より少ない場合は、結果は入力のリスト全体とする。{anchorTerm takeThree}`#eval take 3 ["bolete", "oyster"]`は{anchorInfo takeThree}`["bolete", "oyster"]`に、{anchor takeOne}`#eval take 1 ["bolete", "oyster"]`は{anchorInfo takeOne}`["bolete"]`になるはずである。
 * 型と算数の類似を使って、直積を直和に分配する関数を書け。型は{anchorTerm distr}`α × (β ⊕ γ) → (α × β) ⊕ (α × γ)`である。
 * 型と算数の類似を使って、2倍の乗算を直和に変える関数を書け。型は{anchorTerm distr}`Bool × α → α ⊕ α`である。
