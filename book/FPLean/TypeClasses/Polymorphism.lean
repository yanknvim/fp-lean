module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true



#doc (Manual) "Type Classes and Polymorphism" =>
%%%
tag := "tc-polymorphism"
%%%

ある関数の*任意の*オーバーロードに対して働く関数を書けると役に立つことがある。
たとえば{anchorTerm printlnType}`IO.println`は、{anchorTerm printlnType}`ToString`のインスタンスを持つ任意の型に対して働く。
必要なインスタンスを角括弧で囲んで示す。{anchorTerm printlnType}`IO.println`の型は{anchorTerm printlnType}`{α : Type} → [ToString α] → α → IO Unit`である。
この型は、{anchorTerm printlnType}`IO.println`が{anchorTerm printlnType}`α`型の引数（Leanが自動で決めるべきもの）を取り、{anchorTerm printlnType}`α`に対して使える{anchorTerm printlnType}`ToString`のインスタンスがなければならない、と述べている。
戻り値は{anchorTerm printlnType}`IO`アクションである。


# 多相関数の型を調べる
%%%
tag := "checking-polymorphic-types"
%%%

暗瞑の引数を取る関数や型クラスを使う関数の型を調べるには、追加の記法が要る。
単に次のように書くと、
```anchor printlnMetas
#check (IO.println)
```
メタ変数を含む型が得られる。
```anchorInfo printlnMetas
IO.println : ?m.2620 → IO Unit
```
Leanは暗瞑の引数を見つけようと最善を尽くすので、メタ変数が現れるのは、それに見合う型情報をまだ見つけられなかったという意味である。
関数のシグネチャを理解するには、関数名の前にアットマーク（{anchorTerm printlnNoMetas}`@`）を付けてこの機能を止められる。
```anchor printlnNoMetas
#check @IO.println
```
```anchorInfo printlnNoMetas
@IO.println : {α : Type u_1} → [ToString α] → α → IO Unit
```
{lit}`Type`の後に{lit}`u_1`が付いているが、これはまだ説明していないLeanの機能を使っている。
今はこの{lit}`Type`の引数は無視してよい。

# インスタンスの暗瞑引数を持つ多相関数を定義する
%%%
tag := "defining-polymorphic-functions-with-instance-implicits"
%%%

:::paragraph
リストの要素をすべて合計する関数には二つのインスタンスが要る。{moduleName}`Add`は要素を足せるようにし、{anchorTerm ListSum}`0`に対する{moduleName}`OfNat`のインスタンスは、空のリストで返す安当な値を与える。

```anchor ListSum
def List.sumOfContents [Add α] [OfNat α 0] : List α → α
  | [] => 0
  | x :: xs => x + xs.sumOfContents
```
この関数は、{anchorTerm ListSum}`OfNat α 0`の代わりに{anchorTerm ListSumZ}`Zero α`を要求する形でも定義できる。
両者は同等だが、{anchorTerm ListSumZ}`Zero α`の方が読みやすいことがある。

```anchor ListSumZ
def List.sumOfContents [Add α] [Zero α] : List α → α
  | [] => 0
  | x :: xs => x + xs.sumOfContents
```
:::

:::paragraph

この関数は{anchorTerm fourNats}`Nat`のリストには使える。

```anchor fourNats
def fourNats : List Nat := [1, 2, 3, 4]
```
```anchor fourNatsSum
#eval fourNats.sumOfContents
```
```anchorInfo fourNatsSum
10
```
しかし{anchorTerm fourPos}`Pos`の数のリストには使えない。

```anchor fourPos
def fourPos : List Pos := [1, 2, 3, 4]
```
```anchor fourPosSum
#eval fourPos.sumOfContents
```
```anchorError fourPosSum
failed to synthesize instance of type class
  Zero Pos

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
この関数はLeanの標準ライブラリにもあり、{moduleName}`List.sum`という名前である。

:::

角括弧で指定する必要なインスタンスを*インスタンスの暗瞑引数*と呼ぶ。
舞台裏では、すべての型クラスが、オーバーロードされた操作ごとにフィールドを持つ構造体を定義する。
インスタンスはその構造体型の値であり、各フィールドに実装が入っている。
呼び出しの場所では、Leanがインスタンスの暗瞑引数ごとに渡すべきインスタンスの値を見つける役割を負う。
普通の暗瞑引数とインスタンスの暗瞑引数の最も重要な違いは、Leanが引数の値を見つけるときの戦略である。
普通の暗瞑引数の場合は、Leanは*単一化*という手法を使って、プログラムが型検査を通るような唯一の引数の値を見つける。
この処理は、関数の定義と呼び出しの場所に出てくる具体的な型だけに頼る。
インスタンスの暗瞑引数の場合は、代わりにLeanがインスタンスの値の組み込みの表を参照する。

{anchorName OfNatPos}`Pos`に対する{anchorTerm OfNatPos}`OfNat`のインスタンスが自然数{anchorName OfNatPos}`n`を自動の暗瞑引数として取ったように、インスタンス自身もインスタンスの暗瞑引数を取れる。
{ref "polymorphism"}[多相性の節]では、多相的な点の型を紹介した。

```anchor PPoint
structure PPoint (α : Type) where
  x : α
  y : α
```
点の加法は、対応する{anchorName PPoint}`x`と{anchorName PPoint}`y`のフィールドを足すものであるべきである。
したがって、{anchorName AddPPoint}`PPoint`に対する{anchorName AddPPoint}`Add`のインスタンスには、そのフィールドの型に対する{anchorName AddPPoint}`Add`のインスタンスが要る。
言い換えれば、{anchorName AddPPoint}`PPoint`に対する{anchorName AddPPoint}`Add`のインスタンスは、さらに{anchorName AddPPoint}`α`に対する{anchorName AddPPoint}`Add`のインスタンスを要求する。

```anchor AddPPoint
instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }
```
Leanが二つの点の加法に出会うと、このインスタンスを探して見つける。
次に、{anchorTerm AddPPoint}`Add α`のインスタンスをさらに探す。

このようにして組み立てられるインスタンスの値は、型クラスの構造体型の値である。
再帰的なインスタンス探索が成功すると、別の構造体の値への参照を持つ構造体の値が得られる。
{anchorTerm AddPPointNat}`Add (PPoint Nat)`のインスタンスは、見つかった{anchorTerm AddPPointNat}`Add Nat`のインスタンスへの参照を含む。

この再帰的な探索の仕組みにより、型クラスは単なるオーバーロードされた関数よりずっと強力である。
多相的なインスタンスのライブラリは、望む型さえ与えれば、コンパイラが自分で組み立てるコードの部品の集合である。
インスタンスの引数を取る多相関数は、型クラスの仕組みに対して、舞台裏で補助関数を組み立てるよう求める潜在的な依頼である。
APIの利用者は、必要な部品を手でつなぎ合わせる手間から解放される。


# メソッドと暗瞑引数
%%%
tag := "method-implicit-params"
%%%

{anchorTerm ofNatType}`OfNat.ofNat`の型は意外かもしれない。
その型は{anchorTerm ofNatType}`: {α : Type} → (n : Nat) → [OfNat α n] → α`であり、{anchorTerm ofNatType}`Nat`の引数{anchorTerm ofNatType}`n`が明示的な関数の引数として現れている。
しかし、メソッドの宣言では{anchorName OfNat}`ofNat`の型は単に{anchorName ofNatType}`α`である。
この一見した食い違いは、型クラスを宣言すると実際には次のものができるためである。

 * オーバーロードされた操作の実装を入れる構造体型
 * クラスと同じ名前の名前空間
 * メソッドごとに、インスタンスからその実装を取り出す、クラスの名前空間にある関数

これは、新しい構造体を宣言するとアクセサ関数も宣言されるのと似ている。
主な違いは、構造体のアクセサが構造体の値を明示的な引数として取るのに対し、型クラスのメソッドはインスタンスの値を、Leanが自動で見つけるインスタンスの暗瞑引数として取ることである。

Leanがインスタンスを見つけるには、その引数が使える状態でなければならない。
つまり、型クラスの各引数は、メソッドの、インスタンスより前に現れる引数でなければならない。
これらの引数が暗瞑であると最も便利である。値を探す仕事をLeanがやってくれるためである。
たとえば{anchorTerm addType}`Add.add`の型は{anchorTerm addType}`{α : Type} → [Add α] → α → α → α`である。
この場合、型引数{anchorTerm addType}`α`は暗瞑にできる。{anchorTerm addType}`Add.add`の引数が、利用者が意図した型の情報を与えるためである。
その型を使って{anchorTerm addType}`Add`のインスタンスを探せる。

しかし{anchorName ofNatType}`OfNat.ofNat`の場合は、解読すべき{moduleName}`Nat`のリテラルが、他のどの引数の型の一部としても現れない。
つまり、暗瞑の引数{anchorName ofNatType}`n`を推測しようとするとき、Leanが使える情報がない。
それでは非常に使いにくいAPIになる。
そのため、このような場合は、クラスのメソッドに明示的な引数を使う。



# 練習問題
%%%
tag := "type-class-polymorphism-exercises"
%%%

## 偶数のリテラル
%%%
tag := none
%%%


{ref "even-numbers-ex"}[前の節の練習問題]で作った偶数のデータ型について、再帰的なインスタンス探索を使う{anchorName ofNatType}`OfNat`のインスタンスを書け。

## 再帰的なインスタンス探索の深さ
%%%
tag := none
%%%

Leanコンパイラが再帰的なインスタンス探索を試みる回数には上限がある。
そのため、前の練習問題で定義する偶数のリテラルの大きさにも上限ができる。
その上限がいくつかを実験で突き止めよ。
