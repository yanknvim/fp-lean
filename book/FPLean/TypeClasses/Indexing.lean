module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true

#doc (Manual) "Arrays and Indexing" =>


{ref "props-proofs-indexing"}[幕間]では、リストの要素を位置で参照するための記法を説明した。
この記法も型クラスで定められており、さまざまな型に使える。

# 配列
%%%
tag := "array-indexing"
%%%

たとえば、Leanの配列はほとんどの用途で連結リストよりずっと効率がよい。
Leanでは、{anchorTerm arrVsList}`Array α`型は{anchorName arrVsList}`α`型の値を入れる大きさ可変の配列で、Javaの{java}`ArrayList`、C++の{cpp}`std::vector`、Rustの{rust}`Vec`によく似ている。
{anchorName arrVsList}`cons`コンストラクタを使うたびにポインタをたどる{anchorTerm arrVsList}`List`と違い、配列はメモリ上で連続した領域を占めるので、プロセッサのキャッシュにずっと有利である。
また、配列の値の参照は定数時間で済むが、連結リストの参照は参照する添字に比例した時間がかかる。

Leanのような純粋関数型言語では、データ構造の特定の位置を書き換えられない。
代わりに、望む変更を加えたコピーを作る。
ただし、コピーが常に必要なわけではない。Leanのコンパイラと実行時システムには、配列への参照がただ一つだけのときは、変更を舞台裏で書き換えとして実装できるようにする最適化がある。

配列はリストと同様に書くが、先頭に{lit}`#`を付ける。

```anchor northernTrees
def northernTrees : Array String :=
  #["sloe", "birch", "elm", "oak"]
```
配列に入っている値の個数は{anchorName arrVsList}`Array.size`で分かる。
たとえば{anchorTerm northernTreesSize}`northernTrees.size`は{anchorTerm northernTreesSize}`4`と評価される。
配列の大きさより小さい添字なら、リストと同じく参照の記法で対応する値を求められる。
つまり{anchorTerm northernTreesTwo}`northernTrees[2]`は{anchorTerm northernTreesTwo}`"elm"`と評価される。
同様に、コンパイラは添字が範囲内にあることの証明を要求し、配列の範囲外の値を参照しようとすると、リストと同じくコンパイル時のエラーになる。
たとえば{anchorTerm northernTreesEight}`northernTrees[8]`は次のようになる。
```anchorError northernTreesEight
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
⊢ 8 < northernTrees.size
```

# 空でないリスト
%%%
tag := "non-empty-list-indexing"
%%%

空でないリストを表すデータ型は、リストの先頭のフィールドと、普通の（空になりうる）リストである残りのフィールドを持つ構造体として定義できる。

```anchor NonEmptyList
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
```
たとえば、空でないリスト{moduleName}`idahoSpiders`（米国アイダホ州に自生するクモの種をいくつか含む）は、{anchorTerm firstSpider}`"Banded Garden Spider"`と、それに続く4種のクモ、合わせて5種のクモから成る。

```anchor idahoSpiders
def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}
```

このリストの特定の添字の値を再帰関数で参照するには、三つの場合を考える必要がある。
 1. 添字が{anchorTerm NEListGetHuh}`0`なら、リストの先頭を返す。
 2. 添字が{anchorTerm NEListGetHuh}`n + 1`で、残りが空なら、添字は範囲外である。
 3. 添字が{anchorTerm NEListGetHuh}`n + 1`で、残りが空でなければ、残りと{anchorTerm NEListGetHuh}`n`に対して関数を再帰的に呼び出せる。

たとえば、{moduleName}`Option`を返す参照関数は次のように書ける。

```anchor NEListGetHuh
def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | {head := _, tail := []}, _ + 1 => none
  | {head := _, tail := h :: t}, n + 1 => get? {head := h, tail := t} n
```
パターンマッチングの各場合が、上の可能性のそれぞれに対応する。
{anchorName NEListGetHuh}`get?`への再帰呼び出しに{moduleName}`NonEmptyList`の名前空間の修飾が要らないのは、定義の本体が暗黙にその定義の名前空間に入るためである。
この関数の別の書き方では、添字が0より大きいときにリストの参照{anchorTerm NEListGetHuhList}`xs.tail[n]?`を使う。

```anchor NEListGetHuhList
def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | xs, n + 1 => xs.tail[n]?
```

リストの要素が一つなら、有効な添字は{anchorTerm nats}`0`だけである。
要素が二つなら、{anchorTerm nats}`0`と{anchorTerm nats}`1`の両方が有効な添字である。
要素が三つなら、{anchorTerm nats}`0`、{anchorTerm nats}`1`、{anchorTerm nats}`2`が有効な添字である。
言い換えれば、空でないリストへの有効な添字は、リストの長さより真に小さい自然数であり、これは残りの長さ以下である。

添字が範囲内にあるとはどういうことかの定義は{kw}`abbrev`で書くべきである。添字が許容される証拠を見つけるのに使うタクティクは数の不等式を解けるが、{moduleName}`NonEmptyList.inBounds`という名前については何も知らないためである。

```anchor inBoundsNEList
abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length
```
この関数は、真にも偽にもなりうる命題を返す。
たとえば{moduleName}`idahoSpiders`に対して{anchorTerm spiderBoundsChecks}`2`は範囲内だが、{anchorTerm spiderBoundsChecks}`5`は範囲外である。

```anchor spiderBoundsChecks
theorem atLeastThreeSpiders : idahoSpiders.inBounds 2 := by decide

theorem notSixSpiders : ¬idahoSpiders.inBounds 5 := by decide
```
論理否定の演算子は優先順位が非常に低いので、{anchorTerm spiderBoundsChecks}`¬idahoSpiders.inBounds 5`は{anchorTerm spiderBoundsChecks'}`¬(idahoSpiders.inBounds 5)`と同じである。


この事実を使うと、添字が有効である証拠を要求し、したがって{moduleName}`Option`を返さなくてよい参照関数を、証拠をコンパイル時に検査するリスト版に委譲する形で書ける。

```anchor NEListGet
def NonEmptyList.get (xs : NonEmptyList α)
    (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]
```
もちろん、たまたま同じ証拠を使える標準ライブラリの関数に委譲するのではなく、この関数が証拠を直接使うように書くこともできる。
それには、証明と命題を扱う技法が必要であり、本書の後半で説明する。


# 参照のオーバーロード
%%%
tag := "overloading-indexing"
%%%

コレクション型の参照の記法は、{anchorName GetElem}`GetElem`型クラスのインスタンスを定義してオーバーロードできる。
柔軟にするため、{anchorName GetElem}`GetElem`は四つの引数を持つ。
 * コレクションの型
 * 添字の型
 * コレクションから取り出す要素の型
 * 添字が範囲内にある証拠として何が認められるかを定める関数

要素の型と証拠の関数はどちらも出力パラメータである。
{anchorName GetElem}`GetElem`は{anchorName GetElem}`getElem`というメソッドを一つだけ持ち、コレクションの値、添字の値、添字が範囲内にある証拠を引数に取って要素を返す。

```anchor GetElem
class GetElem
    (coll : Type)
    (idx : Type)
    (item : outParam Type)
    (inBounds : outParam (coll → idx → Prop)) where
  getElem : (c : coll) → (i : idx) → inBounds c i → item
```

{anchorTerm GetElemNEList}`NonEmptyList α`の場合は、これらの引数は次のようになる。
 * コレクションは{anchorTerm GetElemNEList}`NonEmptyList α`
 * 添字の型は{anchorName GetElemNEList}`Nat`
 * 要素の型は{anchorName GetElemNEList}`α`
 * 添字が残りの長さ以下なら範囲内である

実際、{anchorTerm GetElemNEList}`GetElem`のインスタンスは{anchorTerm GetElemNEList}`NonEmptyList.get`にそのまま委譲できる。

```anchor GetElemNEList
instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get
```
このインスタンスにより、{anchorTerm GetElemNEList}`NonEmptyList`は{moduleName}`List`と同じくらい便利に使える。
{anchorTerm firstSpider}`idahoSpiders.head`を評価すると{anchorTerm firstSpider}`"Banded Garden Spider"`になり、{anchorTerm tenthSpider}`idahoSpiders[9]`はコンパイル時のエラーになる。
```anchorError tenthSpider
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
⊢ idahoSpiders.inBounds 9
```

{anchorTerm ListPosElem}`GetElem`型クラスではコレクションの型と添字の型がどちらも入力パラメータなので、既存のコレクションに対して新しい型を添字に使える。
正の数の型{anchorTerm ListPosElem}`Pos`は{anchorTerm ListPosElem}`List`の添字として十分に安当だが、最初の要素を指せないという但し書きが付く。
次の{anchorTerm ListPosElem}`GetElem`のインスタンスにより、リストの要素を求めるのに{moduleName}`Nat`と同じくらい便利に{anchorTerm ListPosElem}`Pos`を使える。

```anchor ListPosElem
instance : GetElem (List α) Pos α
    (fun list n => list.length > n.toNat) where
  getElem (xs : List α) (i : Pos) ok := xs[i.toNat]
```

数値でない添字にも意味があることがある。
たとえば、点のフィールドを選ぶのに{moduleName}`Bool`を使える。{moduleName}`false`が{anchorTerm PPointBoolGetElem}`x`、{moduleName}`true`が{anchorTerm PPointBoolGetElem}`y`に対応する。

```anchor PPointBoolGetElem
instance : GetElem (PPoint α) Bool α (fun _ _ => True) where
  getElem (p : PPoint α) (i : Bool) _ :=
    if not i then p.x else p.y
```
この場合、どちらの真偽値も有効な添字である。
取りうる{moduleName}`Bool`がすべて範囲内なので、証拠は真の命題{moduleName}`True`そのものである。
