module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true

#doc (Manual) "Controlling Instance Search" =>
%%%
tag := "out-params"
%%%

{moduleName}`Add`クラスのインスタンスがあれば、{moduleName}`Pos`型の二つの式を手軽に足して、別の{moduleName}`Pos`を作れる。
しかし多くの場合、引数の型が異なってもよい*異種の*演算子のオーバーロードを許す方が、柔軟で役に立つ。
たとえば、{moduleName}`Nat`に{moduleName}`Pos`を足しても、{moduleName}`Pos`に{moduleName}`Nat`を足しても、結果は必ず{moduleName}`Pos`になる。

```anchor addNatPos
def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => Pos.succ (addNatPos n p)

def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => Pos.succ (addPosNat p n)
```
これらの関数を使えば自然数と正の数を足せるが、{moduleName}`Add`型クラスでは使えない。{moduleName}`add`の二つの引数が同じ型であることを前提としているためである。

# 異種のオーバーロード
%%%
tag := "heterogeneous-operators"
%%%

{ref "overloaded-addition"}[加法のオーバーロード]の節で述べたように、Leanには加法を異種でオーバーロードする{anchorName chapterIntro}`HAdd`という型クラスがある。
{anchorName chapterIntro}`HAdd`クラスは三つの型引数を取る。二つの引数の型と、戻り値の型である。
{anchorTerm haddInsts}`HAdd Nat Pos Pos`と{anchorTerm haddInsts}`HAdd Pos Nat Pos`のインスタンスがあれば、型を混ぜるのに普通の加法の記法を使える。

```anchor haddInsts
instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat
```
上の二つのインスタンスがあれば、次の例は動作する。
```anchor posNatEx
#eval (3 : Pos) + (5 : Nat)
```
```anchorInfo posNatEx
8
```
```anchor natPosEx
#eval (3 : Nat) + (5 : Pos)
```
```anchorInfo natPosEx
8
```

:::paragraph
{anchorName chapterIntro}`HAdd`型クラスの定義は、対応するインスタンスを添えた次の{moduleName}`HPlus`の定義とよく似ている。

```anchor HPlus
class HPlus (α : Type) (β : Type) (γ : Type) where
  hPlus : α → β → γ
```

```anchor HPlusInstances
instance : HPlus Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus Pos Nat Pos where
  hPlus := addPosNat
```
しかし、{moduleName}`HPlus`のインスタンスは{anchorName chapterIntro}`HAdd`のインスタンスよりずっと役に立たない。
これらのインスタンスを{kw}`#eval`で使おうとすると、エラーになる。
```anchor hPlusOops
#eval toString (HPlus.hPlus (3 : Pos) (5 : Nat))
```
```anchorError hPlusOops
typeclass instance problem is stuck
  HPlus Pos Nat ?m.6

Note: Lean will not try to resolve this typeclass instance problem because the third type argument to `HPlus` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
```
このメッセージは、型にメタ変数があり、Leanにそれを解く手立てがないために起きる、と述べている。
:::

{ref "polymorphism"}[多相性の最初の説明]で述べたように、メタ変数は推論できなかったプログラムの未知の部分を表す。
{kw}`#eval`の後に式を書くと、Leanはその型を自動で決めようとする。
この場合は決められなかった。
{anchorName HPlusInstances}`HPlus`の三番目の型引数が不明だったので、Leanは型クラスのインスタンス探索を行えなかった。しかし、その探索だけが式の型を決める手段だったのである。
つまり、{anchorTerm HPlusInstances}`HPlus Pos Nat Pos`のインスタンスは、式の型が{moduleName}`Pos`である場合にしか使えないが、プログラム中にはそのインスタンス自身のほかに、型がそうであるべきことを示すものがない。

この問題の解決策の一つは、式全体に型注釈を付けて三つの型すべてが分かるようにすることである。
```anchor hPlusLotsaTypes
#eval (HPlus.hPlus (3 : Pos) (5 : Nat) : Pos)
```
```anchorInfo hPlusLotsaTypes
8
```
しかし、この解決策は正の数のライブラリの利用者にとってあまり便利ではない。


# 出力パラメータ
%%%
tag := "output-parameters"
%%%

この問題は、{anchorName HPlus}`γ`を*出力パラメータ*として宣言することでも解決できる。
型クラスの引数のほとんどは探索の入力である。インスタンスを選ぶのに使われる。
たとえば{moduleName}`OfNat`のインスタンスでは、型と自然数の両方が、自然数のリテラルの特定の解釈を選ぶのに使われる。
しかし場合によっては、一部の型引数がまだ分からない状態でも探索を始め、探索で見つかったインスタンスを使ってメタ変数の値を決められると便利である。
インスタンス探索を始めるのに要らない引数はその処理の出力であり、{moduleName}`outParam`修飾子で宣言する。

```anchor HPlusOut
class HPlus (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ
```

この出力パラメータがあれば、{anchorName HPlusOut}`γ`を前もって知らなくても、型クラスのインスタンス探索がインスタンスを選べる。
たとえば、
```anchor hPlusWorks
#eval HPlus.hPlus (3 : Pos) (5 : Nat)
```
```anchorInfo hPlusWorks
8
```

出力パラメータは一種の関数を定義するものだと考えると分かりやすい。
出力パラメータを一つ以上持つ型クラスのインスタンスは、入力から出力を求める手順をLeanに与える。
インスタンスを（再帰的に）探す処理は、単なるオーバーロードより強力である。
出力パラメータはプログラム中の他の型を決められ、インスタンス探索は基になるインスタンスの集まりを、その型を持つプログラムに組み立てられる。

# 既定のインスタンス
%%%
tag := "default-instances"
%%%

引数を入力にするか出力にするかで、Leanが型クラス探索を始める状況が変わる。
とくに、すべての入力が分かるまで型クラス探索は起こらない。
しかし場合によっては出力パラメータでは足りず、一部の入力が不明でもインスタンス探索を行うべきことがある。
これは、PythonやKotlinの省略可能な関数引数の既定値に少し似ているが、選ばれるのは*型*の既定値である。

*既定のインスタンス*とは、*入力がすべて分かっていなくても*インスタンス探索で使えるインスタンスである。
このようなインスタンスが使えるときは、使われる。
これにより、未知の型やメタ変数に関するエラーで失敗する代わりに、プログラムが型検査を通ることがある。
一方、既定のインスタンスはインスタンスの選択を予測しにくくする。
とくに、望まない既定のインスタンスが選ばれると、式が期待と違う型になり、プログラムの別の場所で紛らわしい型エラーが起きうる。
既定のインスタンスを使う場所は選んでほしい。

既定のインスタンスが役に立つ例の一つは、{moduleName}`Add`のインスタンスから導ける{anchorName HPlusOut}`HPlus`のインスタンスである。
言い換えれば、普通の加法は、三つの型がたまたま同じである異種の加法の特別な場合である。
これは次のインスタンスで実装できる。

```anchor notDefaultAdd
instance [Add α] : HPlus α α α where
  hPlus := Add.add
```
このインスタンスがあれば、{anchorName notDefaultAdd}`hPlus`を{moduleName}`Nat`のように足せる任意の型に使える。
```anchor hPlusNatNat
#eval HPlus.hPlus (3 : Nat) (5 : Nat)
```
```anchorInfo hPlusNatNat
8
```

しかし、このインスタンスは二つの引数の型がどちらも分かっている場合にしか使われない。
たとえば、
```anchor plusFiveThree
#check HPlus.hPlus (5 : Nat) (3 : Nat)
```
という型が得られる。
```anchorInfo plusFiveThree
HPlus.hPlus 5 3 : Nat
```
これは期待どおりだが、
```anchor plusFiveMeta
#check HPlus.hPlus (5 : Nat)
```
の型にはメタ変数が二つ含まれる。残りの引数の分と、戻り値の型の分である。
```anchorInfo plusFiveMeta
HPlus.hPlus 5 : ?m.15752 → ?m.15754
```

ほとんどの場合、加法の引数を一つ与えたとき、もう一方の引数の型は同じになる。
このインスタンスを既定のインスタンスにするには、{anchorTerm defaultAdd}`default_instance`属性を付ける。

```anchor defaultAdd
@[default_instance]
instance [Add α] : HPlus α α α where
  hPlus := Add.add
```
この既定のインスタンスがあれば、この例はより役に立つ型になる。
```anchor plusFive
#check HPlus.hPlus (5 : Nat)
```
が得られる。

```anchorInfo plusFive
HPlus.hPlus 5 : Nat → Nat
```

オーバーロード可能な異種版と同種版の両方を持つ演算子はどれも、異種版が期待される場面で同種版を使えるようにする既定のインスタンス、という形になっている。
中置演算子は異種版の呼び出しに置き換えられ、可能なときは同種版の既定のインスタンスが選ばれる。

同様に、単に{anchorTerm fiveType}`5`と書くと、{moduleName}`OfNat`のインスタンスを選ぶための情報を待つメタ変数を含む型ではなく、{anchorTerm fiveType}`Nat`になる。
{moduleName}`Nat`に対する{moduleName}`OfNat`のインスタンスが既定のインスタンスだからである。

既定のインスタンスには*優先度*も付けられ、複数の候補があるときにどれが選ばれるかに影響する。
既定のインスタンスの優先度について詳しくは、Leanのマニュアルを参照してほしい。


# 練習問題
%%%
tag := "out-params-exercises"
%%%

両方の成分をそのスカラー倍する{anchorTerm MulPPoint}`HMul (PPoint α) α (PPoint α)`のインスタンスを定義せよ。
{anchorTerm MulPPoint}`Mul α`のインスタンスがある任意の型{anchorName MulPPoint}`α`に対して働くようにする。
たとえば、
```anchor HMulPPoint
#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0
```
となるはずである。
```anchorInfo HMulPPoint
{ x := 5.000000, y := 7.400000 }
```
