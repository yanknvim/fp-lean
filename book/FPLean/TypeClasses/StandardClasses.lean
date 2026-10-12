module
public import VersoManual
import FPLean.Examples



open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true

#doc (Manual) "Standard Classes" =>
%%%
tag := "standard-classes"
%%%


この節では、Leanで型クラスを使ってオーバーロードできるさまざまな演算子と関数を紹介する。
各演算子や関数は、型クラスのメソッドに対応する。
C++と違い、Leanの中置演算子は名前付きの関数の略として定義されている。つまり、新しい型に対してオーバーロードするときは、演算子そのものではなく、その下にある名前（{moduleName}`HAdd.hAdd`など）を使う。

# 算術
%%%
tag := "arithmetic-classes"
%%%

ほとんどの算術演算子には異種の形があり、引数の型が異なってもよく、出力パラメータが結果の式の型を決める。
異種の演算子にはそれぞれ対応する同種の版があり、{lit}`h`の文字を取ると得られる。{moduleName}`HAdd.hAdd`なら{moduleName}`Add.add`である。
次の算術演算子がオーバーロードされている。

:::table +header

*
 -  式
 -  脱糖した形
 -  クラス名
*
 -  {anchorTerm plusDesugar}`x + y`
 -  {anchorTerm plusDesugar}`HAdd.hAdd x y`
 -  {moduleName}`HAdd`
*
 -  {anchorTerm minusDesugar}`x - y`
 -  {anchorTerm minusDesugar}`HSub.hSub x y`
 -  {moduleName}`HSub`
*
 -  {anchorTerm timesDesugar}`x * y`
 -  {anchorTerm timesDesugar}`HMul.hMul x y`
 -  {moduleName}`HMul`
*
 -  {anchorTerm divDesugar}`x / y`
 -  {anchorTerm divDesugar}`HDiv.hDiv x y`
 -  {moduleName}`HDiv`
*
 -  {anchorTerm modDesugar}`x % y`
 -  {anchorTerm modDesugar}`HMod.hMod x y`
 -  {moduleName}`HMod`
*
 -  {anchorTerm powDesugar}`x ^ y`
 -  {anchorTerm powDesugar}`HPow.hPow x y`
 -  {moduleName}`HPow`
*
 -  {anchorTerm negDesugar}`- x`
 -  {anchorTerm negDesugar}`Neg.neg x`
 -  {moduleName}`Neg`


:::

# ビット演算子
%%%
tag := "bitwise-classes"
%%%

Leanには、型クラスでオーバーロードされた標準的なビット演算子がいくつかある。
{anchorTerm UInt8}`UInt8`、{anchorTerm UInt16}`UInt16`、{anchorTerm UInt32}`UInt32`、{anchorTerm UInt64}`UInt64`、{anchorTerm USize}`USize`のような固定幅の型に対するインスタンスがある。
最後のものは、現在のプラットフォームのワード長（通常32ビットか64ビット）である。
次のビット演算子がオーバーロードされている。

:::table +header
*
 -  式
 -  脱糖した形
 -  クラス名

*
 -  {anchorTerm bAndDesugar}`x &&& y`
 -  {anchorTerm bAndDesugar}`HAnd.hAnd x y`
 -  {moduleName}`HAnd`
*
 -  {anchorTerm bOrDesugar}`x ||| y`
 -  {anchorTerm bOrDesugar}`HOr.hOr x y`
 -  {moduleName}`HOr`
*
 -  {anchorTerm bXorDesugar}`x ^^^ y`
 -  {anchorTerm bXorDesugar}`HXor.hXor x y`
 -  {moduleName}`HXor`
*
 -  {anchorTerm complementDesugar}`~~~x`
 -  {anchorTerm complementDesugar}`Complement.complement x`
 -  {moduleName}`Complement`
*
 -  {anchorTerm shrDesugar}`x >>> y`
 -  {anchorTerm shrDesugar}`HShiftRight.hShiftRight x y`
 -  {moduleName}`HShiftRight`
*
 -  {anchorTerm shlDesugar}`x <<< y`
 -  {anchorTerm shlDesugar}`HShiftLeft.hShiftLeft x y`
 -  {moduleName}`HShiftLeft`

:::

{anchorName chapterIntro}`And`と{anchorName chapterIntro}`Or`という名前はすでに論理結合子の名前として使われているので、{anchorName chapterIntro}`HAnd`と{anchorName chapterIntro}`HOr`の同種版は、{anchorName chapterIntro}`And`と{anchorName chapterIntro}`Or`ではなく{anchorName moreOps}`AndOp`と{anchorName moreOps}`OrOp`という名前である。

# 等価性と順序
%%%
tag := "equality-and-ordering"
%%%

二つの値が等しいかを調べるには通常{moduleName}`BEq`クラスを使う。これは「Boolean equality」の略である。
Leanが定理証明器として使われるため、Leanには実質的に二種類の等価演算子がある。
 * {deftech}*ブール値の等価性*は、他のプログラミング言語にあるのと同じ種類の等価性である。二つの値を取り{anchorName CoeBoolProp}`Bool`を返す関数であり、PythonやC#と同じく等号二つで書く。Leanは純粋関数型言語なので、参照の等価性と値の等価性という区別はない。ポインタを直接観察できないからである。
 * {deftech}*命題的等価性*は、二つのものが等しいという数学的な主張である。関数ではなく、証明を受け付ける数学的な主張であり、等号一つで書く。命題的等価性の主張は、その等価性の証拠を分類する型のようなものである。

どちらの等価性も重要であり、用途が異なる。
ブール値の等価性は、二つの値が等しいかどうかをプログラムで判断する必要があるときに役に立つ。
たとえば{anchorTerm boolEqTrue}`"Octopus" ==  "Cuttlefish"`は{anchorTerm boolEqTrue}`false`に、{anchorTerm boolEqFalse}`"Octopodes" ==  "Octo".append "podes"`は{anchorTerm boolEqFalse}`true`に評価される。
関数のようないくつかの値は、等しさを調べられない。
たとえば{anchorTerm functionEq}`(fun (x : Nat) => 1 + x) == (Nat.succ ·)`は次のエラーになる。
```anchorError functionEq
failed to synthesize instance of type class
  BEq (Nat → Nat)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
このメッセージが示すように、{lit}`==`は型クラスでオーバーロードされている。
式{anchorTerm beqDesugar}`x == y`は実際には{anchorTerm beqDesugar}`BEq.beq x y`の略である。

命題的等価性は、プログラムの呼び出しではなく数学的な主張である。
命題はある主張の証拠を記述する型のようなものなので、命題的等価性はブール値の等価性より、{anchorName readFile}`String`や{anchorTerm moreOps}`Nat → List Int`のような型と共通点が多い。
つまり、自動で調べることはできない。
ただし、同じ型を持つ二つの式なら、その等しさはLeanで主張できる。
{anchorTerm functionEqProp}`(fun (x : Nat) => 1 + x) = (Nat.succ ·)`という主張は完全に安当な主張である。
数学の観点では、二つの関数は等しい入力を等しい出力に写すとき等しいので、この主張は真でもある。ただし、Leanにそれを納得させるには1行の証明が要る。

一般に、Leanをプログラミング言語として使うときは、命題よりブール値の関数に留まる方が楽である。
しかし、{moduleName}`Bool`のコンストラクタの名前が{moduleName}`true`と{moduleName}`false`であることからも分かるように、この違いはときに曖昧になる。
命題の中には*決定可能*なものがあり、ブール値の関数と同じように調べられる。
その命題が真か偽かを調べる関数を*決定手続き*と呼び、命題の真偽の*証拠*を返す。
決定可能な命題の例には、自然数の等価性と非等価性、文字列の等価性、それ自体が決定可能な命題の「かつ」と「または」がある。

:::paragraph
Leanでは、{kw}`if`は決定可能な命題に対して働く。
たとえば{anchorTerm twoLessFour}`2 < 4`は命題である。
```anchor twoLessFour
#check 2 < 4
```
```anchorInfo twoLessFour
2 < 4 : Prop
```
それでも、{kw}`if`の条件として書くことはまったく問題ない。
たとえば{anchorTerm ifProp}`if 2 < 4 then 1 else 2`は{moduleName}`Nat`型であり、{anchorTerm ifProp}`1`と評価される。
:::

すべての命題が決定可能なわけではない。
もしそうなら、コンピュータは決定手続きを走らせるだけで任意の真の命題を証明でき、数学者は職を失うことになる。
より正確には、決定可能な命題には{anchorName DecLTLEPos}`Decidable`型クラスのインスタンスがあり、それに決定手続きが入っている。
決定可能でない命題を{anchorName CoeBoolProp}`Bool`のように使おうとすると、{anchorName DecLTLEPos}`Decidable`のインスタンスが見つからずに失敗する。
たとえば{anchorTerm funEqDec}`if (fun (x : Nat) => 1 + x) = (Nat.succ ·) then "yes" else "no"`は次のようになる。
```anchorError funEqDec
failed to synthesize instance of type class
  Decidable ((fun x => 1 + x) = fun x => x.succ)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

次の命題は通常は決定可能であり、型クラスでオーバーロードされている。

:::table +header
*
 -  式
 -  脱糖した形
 -  クラス名
*
 -  {anchorTerm ltDesugar}`x < y`
 -  {anchorTerm ltDesugar}`LT.lt x y`
 -  {moduleName}`LT`
*
 -  {anchorTerm leDesugar}`x ≤ y`
 -  {anchorTerm leDesugar}`LE.le x y`
 -  {moduleName}`LE`
*
 -  {anchorTerm gtDesugar}`x > y`
 -  {anchorTerm gtDesugar}`LT.lt y x`
 -  {moduleName}`LT`
*
 -  {anchorTerm geDesugar}`x ≥ y`
 -  {anchorTerm geDesugar}`LE.le y x`
 -  {moduleName}`LE`
:::

新しい命題の定義はまだ示していないので、{moduleName}`LT`と{moduleName}`LE`のまったく新しいインスタンスを定義するのは難しいかもしれない。
ただし、既存のインスタンスを使って定義できる。
{anchorName LTPos}`Pos`に対する{moduleName}`LT`と{moduleName}`LE`のインスタンスは、{moduleName}`Nat`の既存のインスタンスを使える。

```anchor LTPos
instance : LT Pos where
  lt x y := LT.lt x.toNat y.toNat
```

```anchor LEPos
instance : LE Pos where
  le x y := LE.le x.toNat y.toNat
```
これらの命題は既定では決定可能ではない。Leanがインスタンスを合成するときに命題の定義を展開しないためである。
これは、インスタンスがあれば見つける{anchorName DecLTLEPos}`inferInstance`演算子で橋渡しできる。
型注釈は、{anchorName DecLTLEPos}`inferInstance`に{anchorTerm DecLTLEPos}`Decidable (x.toNat < y.toNat)`と{anchorTerm DecLTLEPos}`Decidable (x.toNat ≤ y.toNat)`のインスタンスを推論するよう指示している。これらは展開後の形である。

```anchor DecLTLEPos
instance {x : Pos} {y : Pos} : Decidable (x < y) :=
  (inferInstance : Decidable (x.toNat < y.toNat))

instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  (inferInstance : Decidable (x.toNat ≤ y.toNat))
```
型検査器は、命題の定義が一致していることを確認する。
取り違えるとエラーになる。
```anchor LTLEMismatch
instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  (inferInstance : Decidable (x.toNat < y.toNat))
```
```anchorError LTLEMismatch
Type mismatch
  inferInstance
has type
  Decidable (x.toNat < y.toNat)
but is expected to have type
  Decidable (x ≤ y)
```

:::paragraph
{lit}`<`、{lit}`==`、{lit}`>`で値を比べるのは効率が悪いことがある。
まず一方が他方より小さいかを調べ、次に等しいかを調べると、大きなデータ構造を二度たどることになりうる。
この問題を解決するため、JavaとC#には標準の{java}`compareTo`と{CSharp}`CompareTo`メソッド（それぞれ）があり、クラスが上書きして三つの操作を一度に実装できる。
これらのメソッドは、受け手が引数より小さければ負の整数、等しければ0、大きければ正の整数を返す。
整数の意味をオーバーロードする代わりに、Leanにはこの三つの可能性を表す組み込みの帰納型がある。
```anchor Ordering
inductive Ordering where
  | lt
  | eq
  | gt
```
{anchorName OrdPos}`Ord`型クラスをオーバーロードしてこの比較を行える。
{anchorName OrdPos}`Pos`の場合、実装は次のようにできる。
```anchor OrdPos
def Pos.comp : Pos → Pos → Ordering
  | Pos.one, Pos.one => Ordering.eq
  | Pos.one, Pos.succ _ => Ordering.lt
  | Pos.succ _, Pos.one => Ordering.gt
  | Pos.succ n, Pos.succ k => comp n k

instance : Ord Pos where
  compare := Pos.comp
```
Javaで{java}`compareTo`が適切な場面では、Leanでは{moduleName}`Ord.compare`を使う。
:::

# ハッシュ
%%%
tag := "hashing"
%%%

JavaとC#には{java}`hashCode`と{CSharp}`GetHashCode`メソッド（それぞれ）があり、ハッシュ表のようなデータ構造で使うための値のハッシュを計算する。
Leanでの対応物は{anchorName Hashable}`Hashable`という型クラスである。

```anchor Hashable
class Hashable (α : Type) where
  hash : α → UInt64
```
ある型の{moduleName}`BEq`インスタンスで二つの値が等しいと見なされるなら、それらのハッシュも同じでなければならない。
言い換えれば、{anchorTerm HashableSpec}`x == y`なら{anchorTerm HashableSpec}`hash x == hash y`である。
{anchorTerm HashableSpec}`x ≠ y`でも{anchorTerm HashableSpec}`hash x`と{anchorTerm HashableSpec}`hash y`が必ず違うとは限らない（{moduleName}`UInt64`の値より{moduleName}`Nat`の値の方が無限に多いからである）。ただし、等しくない値のハッシュが違う可能性が高いほど、ハッシュを使うデータ構造の性能がよくなる。
これはJavaやC#でも同じ期待である。

標準ライブラリには、コンストラクタの異なるフィールドのハッシュを組み合わせるのに使える{anchorTerm mixHash}`mixHash`という型{anchorTerm mixHash}`UInt64 → UInt64 → UInt64`の関数がある。
帰納的データ型の安当なハッシュ関数は、各コンストラクタに一意な数を割り当て、その数を各フィールドのハッシュと混ぜ合わせることで書ける。
たとえば{anchorName HashablePos}`Pos`に対する{anchorName HashablePos}`Hashable`のインスタンスは次のように書ける。

```anchor HashablePos
def hashPos : Pos → UInt64
  | Pos.one => 0
  | Pos.succ n => mixHash 1 (hashPos n)

instance : Hashable Pos where
  hash := hashPos
```

:::paragraph
多相型に対する{anchorTerm HashableNonEmptyList}`Hashable`のインスタンスは、再帰的なインスタンス探索を使える。
{anchorTerm HashableNonEmptyList}`NonEmptyList α`のハッシュは、{anchorName HashableNonEmptyList}`α`をハッシュできるときにだけ計算できる。
```anchor HashableNonEmptyList
instance [Hashable α] : Hashable (NonEmptyList α) where
  hash xs := mixHash (hash xs.head) (hash xs.tail)
```
:::
:::paragraph
二分木では、{anchorName TreeHash}`BEq`と{anchorName TreeHash}`Hashable`の実装に再帰と再帰的なインスタンス探索の両方を使う。

```anchor TreeHash
inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf =>
    true
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
    x == x2 && eqBinTree l l2 && eqBinTree r r2
  | _, _ =>
    false

instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf =>
    0
  | BinTree.branch left x right =>
    mixHash 1
      (mixHash (hashBinTree left)
        (mixHash (hash x)
          (hashBinTree right)))

instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree
```
:::

# 標準クラスの導出
%%%
tag := "deriving-standard-classes"
%%%

{moduleName}`BEq`や{moduleName}`Hashable`のようなクラスのインスタンスは、手で実装するのがかなり面倒なことが多い。
Leanには*インスタンスの導出*という機能があり、コンパイラが多くの型クラスの行儀のよいインスタンスを自動で組み立てられる。
実際、{ref "polymorphism"}[多相性の最初の節]で{anchorName Firewood (module:=Examples.Intro)}`Firewood`を定義したときの{anchorTerm Firewood (module := Examples.Intro)}`deriving Repr`という句が、インスタンスの導出の例である。

インスタンスは二つの方法で導出できる。
一つ目は、構造体や帰納型を定義するときに使える。
その場合は、型の宣言の末尾に{kw}`deriving`を付け、その後にインスタンスを導出したいクラスの名前を書く。
すでに定義済みの型には、単独の{kw}`deriving`コマンドを使える。
{kw}`deriving instance`{lit}` C1, C2, ... `{kw}`for`{lit}` T`と書くと、型{lit}`T`に対する{lit}`C1, C2, ...`のインスタンスを後から導出できる。

{anchorName BEqHashableDerive}`Pos`と{anchorName BEqHashableDerive}`NonEmptyList`に対する{moduleName}`BEq`と{moduleName}`Hashable`のインスタンスは、ごくわずかなコードで導出できる。

```anchor BEqHashableDerive
deriving instance BEq, Hashable for Pos
deriving instance BEq, Hashable for NonEmptyList
```

少なくとも次のクラスのインスタンスを導出できる。

 * {moduleName}`Inhabited`
 * {moduleName}`BEq`
 * {moduleName}`Repr`
 * {moduleName}`Hashable`
 * {moduleName}`Ord`

ただし、導出した{moduleName}`Ord`インスタンスが、アプリケーションで望む順序を正確に与えないこともある。
そのような場合は、{moduleName}`Ord`インスタンスを手で書けばよい。
インスタンスを導出できるクラスの集まりは、Leanに慣れた利用者が拡張できる。

プログラマの生産性とコードの読みやすさが明らかに向上するだけでなく、インスタンスの導出はコードを保守しやすくもする。型の定義が変わるとインスタンスも更新されるためである。
コードの変更をレビューするとき、等価性の検査やハッシュの計算を定型的に何行も直す必要がなければ、データ型の更新を含む変更はずっと読みやすい。

# 連結
%%%
tag := "append-class"
%%%

多くのデータ型には、何らかの連結の演算子がある。
Leanでは、二つの値の連結は{anchorName HAppend}`HAppend`型クラスでオーバーロードされている。算術演算と同じく異種の演算である。

```anchor HAppend
class HAppend (α : Type) (β : Type) (γ : outParam Type) where
  hAppend : α → β → γ
```
{anchorTerm desugarHAppend}`xs ++ ys`という記法は{anchorTerm desugarHAppend}`HAppend.hAppend xs ys`に脱糖される。
同種の場合は、{moduleName}`Append`のインスタンスを実装すれば足りる。通常の形に従う。

```anchor AppendNEList
instance : Append (NonEmptyList α) where
  append xs ys :=
    { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }
```

上のインスタンスを定義すると、
```anchor appendSpiders
#eval idahoSpiders ++ idahoSpiders
```
は次の出力になる。
```anchorInfo appendSpiders
{ head := "Banded Garden Spider",
  tail := ["Long-legged Sac Spider",
           "Wolf Spider",
           "Hobo Spider",
           "Cat-faced Spider",
           "Banded Garden Spider",
           "Long-legged Sac Spider",
           "Wolf Spider",
           "Hobo Spider",
           "Cat-faced Spider"] }
```

同様に、{moduleName}`HAppend`の定義により、普通のリストに空でないリストを連結できる。

```anchor AppendNEListList
instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend xs ys :=
    { head := xs.head, tail := xs.tail ++ ys }
```
このインスタンスがあれば、
```anchor appendSpidersList
#eval idahoSpiders ++ ["Trapdoor Spider"]
```
次のようになる。
```anchorInfo appendSpidersList
{ head := "Banded Garden Spider",
  tail := ["Long-legged Sac Spider", "Wolf Spider", "Hobo Spider", "Cat-faced Spider", "Trapdoor Spider"] }
```

# ファンクタ
%%%
tag := "Functor"
%%%

多相型が{deftech}*ファンクタ*であるとは、その中に入っているすべての要素を関数で変換する{anchorName FunctorDef}`map`という関数のオーバーロードを持つことである。
ほとんどの言語がこの用語を使うが、C#では{anchorName FunctorDef}`map`にあたるものを{CSharp}`System.Linq.Enumerable.Select`と呼ぶ。
たとえば、リストに関数をマップすると、元のリストの各要素をその要素に対する関数の結果で置き換えた新しいリストができる。
{anchorName optionFMeta}`Option`に関数{anchorName optionFMeta}`f`をマップすると、{anchorName optionFMeta}`none`はそのままで、{anchorTerm optionFMeta}`some x`は{anchorTerm optionFMeta}`some (f x)`に置き換わる。

ファンクタの例と、その{anchorName FunctorDef}`Functor`インスタンスが{anchorName FunctorDef}`map`をどうオーバーロードするかを示す。
 * {anchorTerm mapList}`Functor.map (· + 5) [1, 2, 3]` evaluates to {anchorTerm mapList}`[6, 7, 8]`
 * {anchorTerm mapOption}`Functor.map toString (some (List.cons 5 List.nil))` evaluates to {anchorTerm mapOption}`some "[5]"`
 * {anchorTerm mapListList}`Functor.map List.reverse [[1, 2, 3], [4, 5, 6]]` evaluates to {anchorTerm mapListList}`[[3, 2, 1], [6, 5, 4]]`

{anchorName mapList}`Functor.map`はこのよく使う操作には少し長い名前なので、Leanには関数をマップするための中置演算子{lit}`<$>`もある。
先ほどの例は次のように書き直せる。
 * {anchorTerm mapInfixList}`(· + 5) <$> [1, 2, 3]` evaluates to {anchorTerm mapInfixList}`[6, 7, 8]`
 * {anchorTerm mapInfixOption}`toString <$> (some (List.cons 5 List.nil))` evaluates to {anchorTerm mapInfixOption}`some "[5]"`
 * {anchorTerm mapInfixListList}`List.reverse <$> [[1, 2, 3], [4, 5, 6]]` evaluates to {anchorTerm mapInfixListList}`[[3, 2, 1], [6, 5, 4]]`

{anchorTerm FunctorNonEmptyList}`NonEmptyList`に対する{anchorTerm FunctorNonEmptyList}`Functor`のインスタンスでは、{anchorName FunctorNonEmptyList}`map`関数を指定する必要がある。

```anchor FunctorNonEmptyList
instance : Functor NonEmptyList where
  map f xs := { head := f xs.head, tail := f <$> xs.tail }
```
ここで{anchorTerm FunctorNonEmptyList}`map`は、{moduleName}`List`に対する{anchorTerm FunctorNonEmptyList}`Functor`のインスタンスを使って、残りの部分に関数をマップしている。
このインスタンスが{anchorTerm FunctorNonEmptyListA}`NonEmptyList α`ではなく{anchorTerm FunctorNonEmptyList}`NonEmptyList`に対して定義されているのは、引数の型{anchorTerm FunctorNonEmptyListA}`α`が型クラスの解決に何の役割も果たさないためである。
{anchorTerm FunctorNonEmptyList}`NonEmptyList`には、*要素の型が何であっても*関数をマップできる。
{anchorTerm FunctorNonEmptyListA}`α`がクラスの引数なら、{anchorTerm FunctorNonEmptyListA}`NonEmptyList Nat`にだけ働く{anchorTerm FunctorNonEmptyList}`Functor`の版を作れてしまう。しかし、ファンクタであることの一部は、{anchorName FunctorNonEmptyList}`map`がどの要素の型に対しても働くことである。

:::paragraph
{anchorTerm FunctorPPoint}`PPoint`に対する{anchorTerm FunctorPPoint}`Functor`のインスタンスは次のとおりである。

```anchor FunctorPPoint
instance : Functor PPoint where
  map f p := { x := f p.x, y := f p.y }
```
この場合、{anchorName FunctorPPoint}`f`は{anchorName FunctorPPoint}`x`と{anchorName FunctorPPoint}`y`の両方に適用されている。
:::

ファンクタに入っている型自体がファンクタであっても、関数のマップは一層しか下りない。
つまり、{anchorTerm NEPP}`NonEmptyList (PPoint Nat)`に{anchorName FunctorPPoint}`map`を使うとき、マップする関数は{moduleName}`Nat`ではなく{anchorTerm NEPP}`PPoint Nat`を引数に取るべきである。

{anchorName FunctorLaws}`Functor`クラスの定義は、まだ説明していない言語機能をもう一つ使っている。既定のメソッド定義である。
通常、クラスはまとめて意味をなす最小限のオーバーロード可能な操作を定め、そのうえで、オーバーロードされた操作を土台にした、インスタンスの暗瞑引数を持つ多相関数を使って、より大きな機能の集まりを提供する。
たとえば、関数{anchorName concat}`concat`は、要素が連結可能な空でないリストを連結できる。

```anchor concat
def concat [Append α] (xs : NonEmptyList α) : α :=
  let rec catList (start : α) : List α → α
    | [] => start
    | (z :: zs) => catList (start ++ z) zs
  catList xs.head xs.tail
```
しかしクラスによっては、データ型の内部を知ることでより効率よく実装できる操作がある。

そのような場合は、既定のメソッド定義を用意できる。
既定のメソッド定義は、他のメソッドを使ってそのメソッドの既定の実装を与える。
ただし、インスタンスの実装者は、より効率のよいものでこの既定を上書きしてよい。
既定のメソッド定義は、{kw}`class`の定義の中に{lit}`:=`を書く。

{anchorName FunctorDef}`Functor`の場合、マップする関数が引数を無視するとき、{anchorName FunctorDef}`map`をより効率よく実装できる型がある。
引数を無視する関数は、常に同じ値を返すので*定数関数*と呼ばれる。
{anchorName FunctorDef}`Functor`の定義は次のとおりで、{anchorName FunctorDef}`mapConst`に既定の実装がある。

```anchor FunctorDef
class Functor (f : Type → Type) where
  map : {α β : Type} → (α → β) → f α → f β

  mapConst {α β : Type} (x : α) (coll : f β) : f α :=
    map (fun _ => x) coll
```

{moduleName}`BEq`を尊重しない{anchorName HashableSpec}`Hashable`インスタンスが誤りであるのと同じく、関数をマップするときにデータを動かす{moduleName}`Functor`インスタンスも誤りである。
たとえば、{moduleName}`List`に対する誤った{moduleName}`Functor`インスタンスは、引数を捨てて常に空のリストを返したり、リストを反転させたりするかもしれない。
{moduleName}`PPoint`に対する誤った{moduleName}`Functor`インスタンスは、{anchorTerm FunctorPPointBad}`f x`を{anchorName FunctorPPointBad}`x`と{anchorName FunctorPPointBad}`y`の両方のフィールドに入れたり、入れ替えたりするかもしれない。
具体的には、{anchorName FunctorDef}`Functor`インスタンスは二つの規則に従うべきである。
 1. 恒等関数をマップすると、元の引数になる。
 2. 二つの関数の合成をマップすることは、それぞれのマップを合成するのと同じ結果になる。

より形式的には、第一の規則は{anchorTerm FunctorLaws}`id <$> x`が{anchorTerm FunctorLaws}`x`に等しいと述べている。
第二の規則は、{anchorTerm FunctorLaws}`map (fun y => f (g y)) x`が{anchorTerm FunctorLaws}`map f (map g x)`に等しいと述べている。
合成{anchorTerm compDef}`f ∘ g`は{anchorTerm compDef}`fun y => f (g y)`とも書ける。
これらの規則は、データを動かしたり一部を削除したりする{anchorName FunctorDef}`map`の実装を防ぐ。

# 出会うかもしれないメッセージ
%%%
tag := "standard-classes-messages"
%%%

Leanがすべてのクラスのインスタンスを導出できるわけではない。
たとえば、次のコードは、
```anchor derivingNotFound
deriving instance ToString for NonEmptyList
```
次のエラーになる。
```anchorError derivingNotFound
No deriving handlers have been implemented for class `ToString`
```
{anchorTerm derivingNotFound}`deriving instance`を呼び出すと、Leanは型クラスのインスタンス用のコード生成器の内部の表を参照する。
コード生成器が見つかれば、与えられた型に対してそれを呼び出してインスタンスを作る。
しかしこのメッセージは、{anchorName derivingNotFound}`ToString`に対するコード生成器が見つからなかったという意味である。

# 練習問題
%%%
tag := "standard-classes-exercises"
%%%

 * {anchorTerm moreOps}`HAppend (List α) (NonEmptyList α) (NonEmptyList α)`のインスタンスを書いて試せ。
 * 二分木のデータ型に対する{anchorTerm FunctorLaws}`Functor`インスタンスを実装せよ。
