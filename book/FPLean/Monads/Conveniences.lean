module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads.Conveniences"

#doc (Manual) "Additional Conveniences" =>
%%%
tag := "monads-conveniences"
%%%

# 引数の型の共有
%%%
tag := "shared-argument-types"
%%%

同じ型の引数を複数取る関数を定義するときは、両方とも同じコロンの前に書ける。
たとえば、

```anchor equalHuhOld
def equal? [BEq α] (x : α) (y : α) : Option α :=
  if x == y then
    some x
  else
    none
```
次のように書ける。

```anchor equalHuhNew
def equal? [BEq α] (x y : α) : Option α :=
  if x == y then
    some x
  else
    none
```
型シグネチャが大きいときには特に役に立つ。

# 先頭のドット記法
%%%
tag := "leading-dot-notation"
%%%

帰納型のコンストラクタは名前空間に入っている。
これにより、関連する複数の帰納型が同じコンストラクタ名を使えるが、プログラムが冗長になることもある。
問題の帰納型が分かっている文脈では、コンストラクタの名前の前にドットを付けて名前空間を省ける。Leanは期待される型を使ってコンストラクタ名を解決する。
たとえば、二分木を反転する関数は次のように書ける。

```anchor mirrorOld
def BinTree.mirror : BinTree α → BinTree α
  | BinTree.leaf => BinTree.leaf
  | BinTree.branch l x r => BinTree.branch (mirror r) x (mirror l)
```
名前空間を省くとかなり短くなるが、Leanコンパイラを備えないコードレビューツールのような場面ではプログラムが読みにくくなる。

```anchor mirrorNew
def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)
```

式の期待される型を使って名前空間の曖昧さを解消するのは、コンストラクタ以外の名前にも当てはまる。
{anchorName BinTreeEmpty}`BinTree.empty`を{anchorName BinTreeEmpty}`BinTree`を作る別の方法として定義すれば、これもドット記法で使える。

```anchor BinTreeEmpty
def BinTree.empty : BinTree α := .leaf
```
```anchor emptyDot
#check (.empty : BinTree Nat)
```
```anchorInfo emptyDot
BinTree.empty : BinTree Nat
```

# またはパターン
%%%
tag := "or-patterns"
%%%

{kw}`match`式のように複数のパターンを書ける文脈では、複数のパターンが同じ結果の式を共有できる。
曜日を表すデータ型{anchorName Weekday}`Weekday`を考える。

```anchor Weekday
inductive Weekday where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
deriving Repr
```

パターンマッチングでその日が週末かどうかを調べられる。

```anchor isWeekendA
def Weekday.isWeekend (day : Weekday) : Bool :=
  match day with
  | Weekday.saturday => true
  | Weekday.sunday => true
  | _ => false
```
これはコンストラクタのドット記法を使えばすでに簡略化できる。

```anchor isWeekendB
def Weekday.isWeekend (day : Weekday) : Bool :=
  match day with
  | .saturday => true
  | .sunday => true
  | _ => false
```
週末の二つのパターンは結果の式（{anchorName isWeekendC}`true`）が同じなので、一つにまとめられる。

```anchor isWeekendC
def Weekday.isWeekend (day : Weekday) : Bool :=
  match day with
  | .saturday | .sunday => true
  | _ => false
```
さらに、引数に名前を付けない版に簡略化できる。

```anchor isWeekendD
def Weekday.isWeekend : Weekday → Bool
  | .saturday | .sunday => true
  | _ => false
```

裏では、結果の式が各パターンに複製されるだけである。
つまりパターンは変数を束縛できる。次の例は、どちらの側も同じ型の値を持つ直和型から{anchorName SumNames}`inl`と{anchorName SumNames}`inr`のコンストラクタを取り除く。

```anchor condense
def condense : α ⊕ α → α
  | .inl x | .inr x => x
```
結果の式が複製されるので、パターンが束縛する変数の型が同じである必要はない。
複数の型で働くオーバーロードされた関数を使えば、異なる型の変数を束縛するパターンに共通して働く一つの結果の式を書ける。

```anchor stringy
def stringy : Nat ⊕ Weekday → String
  | .inl x | .inr x => s!"It is {repr x}"
```
実際には、すべてのパターンに共通する変数だけが結果の式で参照できる。結果はどのパターンについても意味をなす必要があるためである。
{anchorName getTheNat}`getTheNat`では{anchorName getTheNat}`n`だけが参照でき、{anchorName getTheNat}`x`や{anchorName getTheNat}`y`を使おうとするとエラーになる。

```anchor getTheNat
def getTheNat : (Nat × α) ⊕ (Nat × β) → Nat
  | .inl (n, x) | .inr (n, y) => n
```
似た定義で{anchorName getTheAlpha}`x`を参照しようとすると、二つ目のパターンでは{anchorName getTheAlpha}`x`が使えないのでエラーになる。
```anchor getTheAlpha
def getTheAlpha : (Nat × α) ⊕ (Nat × α) → α
  | .inl (n, x) | .inr (n, y) => x
```
```anchorError getTheAlpha
Unknown identifier `x`
```

結果の式が実質的にパターンマッチの各枝にコピーされるという事実は、驚くような振る舞いを生むことがある。
たとえば次の定義は受け付けられる。結果の式の{anchorName SumNames}`inr`の版が、大域的な{anchorName getTheString}`str`の定義を参照するためである。

```anchor getTheString
def str := "Some string"

def getTheString : (Nat × String) ⊕ (Nat × β) → String
  | .inl (n, str) | .inr (n, y) => str
```
この関数を両方のコンストラクタについて呼ぶと、紛らわしい振る舞いが現れる。
一つ目の場合は、{anchorName getTheString}`β`をどの型にすべきかをLeanに伝える型注釈が要る。
```anchor getOne
#eval getTheString (.inl (20, "twenty") : (Nat × String) ⊕ (Nat × String))
```
```anchorInfo getOne
"twenty"
```
二つ目の場合は、大域的な定義が使われる。
```anchor getTwo
#eval getTheString (.inr (20, "twenty"))
```
```anchorInfo getTwo
"Some string"
```

またはパターンを使うと、{anchorName isWeekendD}`Weekday.isWeekend`のように、定義を大幅に簡単にして明快さを増せる。
紛らわしい振る舞いを生む可能性があるので、使うときは注意するのがよい。特に、複数の型の変数や、重なりのない変数の集合が関わるときには注意が要る。
