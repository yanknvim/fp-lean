module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Universes"

#doc (Manual) "Universes" =>
%%%
tag := "universe-levels"
%%%

簡単のため、この本はこれまでLeanの重要な機能である*宇宙*に目をつぶってきた。
宇宙とは、他の型を分類する型である。
そのうち二つはなじみがある。{anchorTerm TypeType}`Type`と{anchorTerm PropType}`Prop`である。
{anchorTerm SomeTypes}`Type`は、{anchorName SomeTypes}`Nat`、{anchorTerm SomeTypes}`String`、{anchorTerm SomeTypes}`Int → String × Char`、{anchorTerm SomeTypes}`IO Unit`のような普通の型を分類する。
{anchorTerm PropType}`Prop`は、{anchorTerm SomeTypes}`"nisse" = "elf"`や{anchorTerm SomeTypes}`3 > 2`のような、真にも偽にもなりうる命題を分類する。
{anchorTerm PropType}`Prop`の型は{anchorTerm SomeTypes}`Type`である。
```anchor PropType
#check Prop
```
```anchorInfo PropType
Prop : Type
```

技術上の理由から、この二つより多くの宇宙が要る。
特に、{anchorTerm SomeTypes}`Type`はそれ自体が{anchorTerm SomeTypes}`Type`にはなれない。
そうなると論理的な逆理を構成できてしまい、定理証明器としてのLeanの有用性が損なわれる。

このことの形式的な論証は*ジラールの逆理*として知られている。
これは、*ラッセルの逆理*としてよりよく知られる逆理と関係がある。初期の集合論が矛盾していたことを示すのに使われたものである。
これらの集合論では、集合は性質によって定義できた。
たとえば、すべての赤いものの集合、すべての果物の集合、すべての自然数の集合、さらにはすべての集合の集合がありうる。
集合が与えられれば、ある要素がそれに含まれるかどうかを問える。
たとえば、ルリツグミはすべての赤いものの集合には含まれないが、すべての赤いものの集合はすべての集合の集合に含まれる。
実際、すべての集合の集合はそれ自体を含む。

それ自体を含まないすべての集合の集合はどうだろうか。
これはすべての赤いものの集合を含む。すべての赤いものの集合はそれ自体が赤くないためである。
これはすべての集合の集合を含まない。すべての集合の集合がそれ自体を含むためである。
では、これはそれ自体を含むだろうか。
それ自体を含むなら、それ自体を含めない。
しかし含まないなら、含まねばならない。

これは矛盾であり、最初の前提のどこかが間違っていたことを示している。
特に、任意の性質を与えて集合を構成できるようにするのは強力すぎた。
後の版の集合論では、逆理を取り除くために集合の構成を制限している。

{anchorTerm SomeTypes}`Type`に{anchorTerm SomeTypes}`Type`という型を割り当てる依存型理論では、関連する逆理を構成できる。
Leanが無矛盾な論理的な基礎を持ち、数学の道具として使えるようにするには、{anchorTerm SomeTypes}`Type`に別の型が必要である。
その型は{anchorTerm SomeTypes}`Type 1`と呼ばれる。
```anchor TypeType
#check Type
```
```anchorInfo TypeType
Type : Type 1
```
同様に、{anchorTerm Type1Type}`Type 1`は{anchorTerm Type1Type}`Type 2`、{anchorTerm Type2Type}`Type 2`は{anchorTerm Type2Type}`Type 3`、{anchorTerm Type3Type}`Type 3`は{anchorTerm Type3Type}`Type 4`、以下同様である。

関数型は、引数の型と戻り値の型の両方を含められる最小の宇宙に入る。
つまり、{anchorTerm NatNatType}`Nat → Nat`は{anchorTerm NatNatType}`Type`、{anchorTerm Fun00Type}`Type → Type`は{anchorTerm Fun00Type}`Type 1`、{anchorTerm Fun12Type}`Type 1 → Type 2`は{anchorTerm Fun12Type}`Type 3`である。

この規則には例外が一つある。
関数の戻り値の型が{anchorTerm PropType}`Prop`なら、引数が{anchorTerm SomeTypes}`Type`や{anchorTerm SomeTypes}`Type 1`のようなより大きな宇宙にあっても、関数型全体が{anchorTerm PropType}`Prop`に入る。
特に、普通の型を持つ値についての述語は{anchorTerm PropType}`Prop`に入る。
たとえば、型{anchorTerm FunPropType}`(n : Nat) → n = n + 0`は、{anchorTerm SomeTypes}`Nat`から、それがそれ自身に0を足したものと等しいという証拠への関数を表す。
{anchorTerm SomeTypes}`Nat`は{anchorTerm SomeTypes}`Type`にあるが、この規則によりこの関数型は{anchorTerm FunPropType}`Prop`にある。
同様に、{anchorTerm SomeTypes}`Type`は{anchorTerm SomeTypes}`Type 1`にあるが、関数型{anchorTerm FunTypePropType}`Type → 2 + 2 = 4`はやはり{anchorTerm FunTypePropType}`Prop`にある。

# 利用者が定義する型
%%%
tag := "inductive-type-universes"
%%%

構造体と帰納的データ型は、特定の宇宙に属するものとして宣言できる。
そしてLeanは、各データ型が、それ自身の型を含めないだけの大きさの宇宙にあることで逆理を避けているかを調べる。
たとえば次の宣言では、{anchorName MyList1}`MyList`が{anchorTerm SomeTypes}`Type`に属するものとして宣言され、その型引数{anchorName MyList1}`α`も同様である。

```anchor MyList1
inductive MyList (α : Type) : Type where
  | nil : MyList α
  | cons : α → MyList α → MyList α
```
{anchorTerm MyList1Type}`MyList`自体は{anchorTerm MyList1Type}`Type → Type`である。
つまり、実際の型を中に入れるのには使えない。そうするとその引数が{anchorTerm SomeTypes}`Type`になり、それは{anchorTerm SomeTypes}`Type 1`だからである。
```anchor myListNat1Err
def myListOfNat : MyList Type :=
  .cons Nat .nil
```
```anchorError myListNat1Err
Application type mismatch: The argument
  Type
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1` in the application
  MyList Type
```

{anchorName MyList2}`MyList`を、その引数が{anchorTerm MyList2}`Type 1`になるように直すと、Leanに拒否される定義になる。
```anchor MyList2
inductive MyList (α : Type 1) : Type where
  | nil : MyList α
  | cons : α → MyList α → MyList α
```
```anchorError MyList2
Invalid universe level in constructor `MyList.cons`: Parameter has type
  α
at universe level
  2
which is not less than or equal to the inductive type's resulting universe level
  1
```
このエラーは、型{anchorName MyList2}`α`を持つ{anchorTerm MyList2}`cons`の引数が{anchorName MyList2}`MyList`より大きな宇宙から来ているために起きる。
{anchorName MyList2}`MyList`自体を{anchorTerm SomeTypes}`Type 1`に置けばこの問題は解決するが、{anchorTerm SomeTypes}`Type`を期待する文脈で{anchorName MyList2}`MyList`を使いにくくなるという代償を払う。

データ型が許されるかどうかを定める具体的な規則はいくらか複雑である。
一般には、データ型をその引数のうち最も大きなものと同じ宇宙から始めるのが最も簡単である。
そしてLeanがその定義を拒否したら、その段階を一つ上げると、たいていは通る。

# 宇宙多相
%%%
tag := "universe-polymorphism"
%%%

データ型を特定の宇宙で定義すると、コードが重複することがある。
{anchorName MyList1}`MyList`を{anchorTerm MyList1Type}`Type → Type`に置くと、実際の型のリストには使えない。
これを{anchorTerm MyList15Type}`Type 1 → Type 1`に置くと、型のリストのリストには使えない。
{anchorTerm SomeTypes}`Type`、{anchorTerm SomeTypes}`Type 1`、{anchorTerm Type2Type}`Type 2`などに版を作るためにデータ型をコピーして貼り付ける代わりに、*宇宙多相*と呼ばれる機能を使えば、これらのどの宇宙でも具体化できる単一の定義を書ける。

普通の多相型は、定義の中で型の代わりに変数を使う。
これによりLeanが変数を違う形で埋められ、これらの定義をさまざまな型で使える。
同様に、宇宙多相は定義の中で宇宙の代わりに変数を使えるようにし、Leanがそれを違う形で埋められるようにして、さまざまな宇宙で使えるようにする。
型引数に慣例としてギリシア文字を使うのと同じように、宇宙の引数には慣例として{lit}`u`、{lit}`v`、{lit}`w`を使う。

この{anchorName MyList3}`MyList`の定義は特定の宇宙の段階を指定せず、任意の段階を表す変数{anchorTerm MyList3}`u`を使う。
得られたデータ型を{anchorTerm SomeTypes}`Type`で使うなら{anchorTerm MyList3}`u`は{lit}`0`、{anchorTerm Fun12Type}`Type 3`で使うなら{anchorTerm MyList3}`u`は{lit}`3`である。

```anchor MyList3
inductive MyList (α : Type u) : Type u where
  | nil : MyList α
  | cons : α → MyList α → MyList α
```

この定義により、同じ{anchorName MyList3}`MyList`の定義を、実際の自然数も自然数の型自体も入れるのに使える。

```anchor myListOfNat3
def myListOfNumbers : MyList Nat :=
  .cons 0 (.cons 1 .nil)

def myListOfNat : MyList Type :=
  .cons Nat .nil
```
それ自体を入れることもできる。

```anchor myListOfList3
def myListOfList : MyList (Type → Type) :=
  .cons MyList .nil
```

これで論理的な逆理を書けるようになるように思える。
何しろ、宇宙の仕組みの狙いは自己言及的な型を排除することにある。
しかし裏では、{anchorName MyList3}`MyList`が現れるたびに宇宙の段階の引数が与えられている。
本質的には、{anchorName MyList3}`MyList`の宇宙多相な定義は各段階にデータ型の*複製*を作っており、段階の引数がどの複製を使うかを選ぶ。
これらの段階の引数はドットと波括弧で書き、{anchorTerm MyListDotZero}`MyList.{0} : Type → Type`、{anchorTerm MyListDotOne}`MyList.{1} : Type 1 → Type 1`、{anchorTerm MyListDotTwo}`MyList.{2} : Type 2 → Type 2`となる。

段階を明示的に書くと、先ほどの例は次のようになる。

```anchor myListOfList3Expl
def myListOfNumbers : MyList.{0} Nat :=
  .cons 0 (.cons 1 .nil)

def myListOfNat : MyList.{1} Type :=
  .cons Nat .nil

def myListOfList : MyList.{1} (Type → Type) :=
  .cons MyList.{0} .nil
```

宇宙多相な定義が複数の型を引数に取るときは、最大限の柔軟さのために引数ごとに独自の段階の変数を与えるとよい。
たとえば、段階の引数を一つだけ持つ{anchorName SumNoMax}`Sum`の版は次のように書ける。

```anchor SumNoMax
inductive Sum (α : Type u) (β : Type u) : Type u where
  | inl : α → Sum α β
  | inr : β → Sum α β
```
この定義は複数の段階で使える。

```anchor SumPoly
def stringOrNat : Sum String Nat := .inl "hello"

def typeOrType : Sum Type Type := .inr Nat
```
しかし、両方の引数が同じ宇宙にあることを要求する。
```anchor stringOrTypeLevels
def stringOrType : Sum String Type := .inr Nat
```
```anchorError stringOrTypeLevels
Application type mismatch: The argument
  Type
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1` in the application
  Sum String Type
```

このデータ型は、二つの型引数の宇宙の段階に別々の変数を使い、得られるデータ型がその二つのうち大きいほうにあると宣言すれば、より柔軟にできる。

```anchor SumMax
inductive Sum (α : Type u) (β : Type v) : Type (max u v) where
  | inl : α → Sum α β
  | inr : β → Sum α β
```
これにより{anchorName SumMax}`Sum`を異なる宇宙の引数で使える。

```anchor stringOrTypeSum
def stringOrType : Sum String Type := .inr Nat
```

Leanが宇宙の段階を期待する位置では、次のいずれも書ける。
 * {lit}`0`や{lit}`1`のような具体的な段階
 * {anchorTerm SumMax}`u`や{anchorTerm SumMax}`v`のような段階を表す変数
 * 二つの段階の最大値。段階に{anchorTerm SumMax}`max`を適用して書く。
 * 段階の増加。{anchorTerm someTrueProps}`+ 1`と書く。

## 宇宙多相な定義を書く
%%%
tag := none
%%%

これまで、この本で定義したデータ型はすべて、データの最小の宇宙である{anchorTerm SomeTypes}`Type`にあった。
{anchorName SomeTypes}`List`や{anchorName SumMax}`Sum`のようなLeanの標準ライブラリの多相データ型を紹介するとき、この本は宇宙多相でない版を作った。
実際の版は宇宙多相を使い、型の段階のプログラムとそうでないプログラムの間でコードを再利用できるようにしている。

宇宙多相な型を書くときに従うべき一般的な指針がいくつかある。
第一に、互いに独立な型引数には別々の宇宙の変数を与えるべきである。そうすればその多相的な定義をより多くの種類の引数で使え、コードの再利用の可能性が広がる。
第二に、型全体は通常、すべての宇宙の変数の最大値か、その最大値より一つ大きい段階にある。
まず小さいほうを試すとよい。
最後に、新しい型はできるだけ小さな宇宙に置くとよい。そうすれば他の文脈でより柔軟に使える。
{anchorTerm SomeTypes}`Nat`や{anchorName SomeTypes}`String`のような多相でない型は、直接{anchorTerm Type0Type}`Type 0`に置ける。

## {anchorTerm PropType}`Prop`と多相
%%%
tag := none
%%%


{anchorTerm SomeTypes}`Type`や{anchorTerm SomeTypes}`Type 1`などがプログラムとデータを分類する型を記述するのと同じように、{anchorTerm PropType}`Prop`は論理的な命題を分類する。
{anchorTerm PropType}`Prop`にある型は、ある言明が真であることの説得力のある証拠として何が認められるかを記述する。
命題は多くの点で普通の型に似ている。帰納的に宣言でき、コンストラクタを持て、関数が命題を引数に取れる。
しかし、データ型と違い、ある言明が真である証拠として*どれ*が与えられるかは通常問題ではなく、証拠が与えられる*こと*だけが問題である。
一方、プログラムが{anchorTerm SomeTypes}`Nat`を返すだけでなく、それが*正しい*{anchorTerm SomeTypes}`Nat`であることは非常に重要である。

{anchorTerm PropType}`Prop`は宇宙の階層の一番下にあり、{anchorTerm PropType}`Prop`の型は{anchorTerm SomeTypes}`Type`である。
つまり{anchorTerm PropType}`Prop`は、{anchorTerm SomeTypes}`Nat`と同じ理由で、{anchorName SomeTypes}`List`に与える適切な引数である。
命題のリストは型{anchorTerm SomeTypes}`List Prop`を持つ。

```anchor someTrueProps
def someTruePropositions : List Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]
```
宇宙の引数を明示的に埋めると、{anchorTerm PropType}`Prop`が{anchorTerm SomeTypes}`Type`であることが示される。

```anchor someTruePropsExp
def someTruePropositions : List.{0} Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]
```

裏では、{anchorTerm PropType}`Prop`と{anchorTerm SomeTypes}`Type`は{anchorTerm SomeTypes}`Sort`と呼ばれる単一の階層に統合されている。
{anchorTerm PropType}`Prop`は{anchorTerm sorts}`Sort 0`と同じであり、{anchorTerm Type0Type}`Type 0`は{anchorTerm sorts}`Sort 1`、{anchorTerm SomeTypes}`Type 1`は{anchorTerm sorts}`Sort 2`、以下同様である。
実際、{anchorTerm sorts}`Type u`は{anchorTerm sorts}`Sort (u+1)`と同じである。
Leanでプログラムを書くときには通常関係ないが、ときどきエラーメッセージに現れることがあり、{anchorName sorts}`CoeSort`クラスの名前の由来でもある。
さらに、{anchorTerm PropType}`Prop`が{anchorTerm sorts}`Sort 0`であることで、もう一つの宇宙の演算子が役に立つようになる。
宇宙の段階{lit}`imax u v`は、{anchorTerm sorts}`v`が{lit}`0`のときは{lit}`0`であり、そうでなければ{anchorTerm sorts}`u`と{anchorTerm sorts}`v`の大きいほうである。
{anchorTerm sorts}`Sort`と合わせると、{anchorTerm PropType}`Prop`を返す関数についての特別な規則を、{anchorTerm PropType}`Prop`と{anchorTerm SomeTypes}`Type`の宇宙の間でできるだけ移植しやすくしたいコードを書くときに使える。

# 実際の多相
%%%
tag := none
%%%

この本の残りでは、多相データ型、構造体、クラスの定義は、Leanの標準ライブラリと整合させるために宇宙多相を使う。
これにより、{moduleName}`Functor`、{anchorName next}`Applicative`、{anchorName next}`Monad`クラスの完全な提示が、それらの実際の定義と完全に整合するようになる。
