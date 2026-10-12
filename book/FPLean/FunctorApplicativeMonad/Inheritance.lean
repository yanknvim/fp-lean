module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.FunctorApplicativeMonad"

#doc (Manual) "Structures and Inheritance" =>
%%%
tag := "structure-inheritance"
%%%

{anchorName ApplicativeLaws}`Functor`、{anchorName ApplicativeLaws}`Applicative`、{anchorName ApplicativeLaws}`Monad`の完全な定義を理解するには、もう一つのLeanの機能が要る。構造体の継承である。
構造体の継承により、ある構造体型が別の構造体のインターフェースと、追加のフィールドを提供できる。
分類上の明確な関係がある概念をモデル化するときに役に立つ。
たとえば、伝説の生き物のモデルを考えよう。
大きいものもいれば小さいものもいる。

```anchor MythicalCreature
structure MythicalCreature where
  large : Bool
deriving Repr
```
裏では、{anchorName MythicalCreature}`MythicalCreature`構造体を定義すると、{anchorName MythicalCreatureMore}`mk`という単一のコンストラクタを持つ帰納型が作られる。
```anchor MythicalCreatureMk
#check MythicalCreature.mk
```
```anchorInfo MythicalCreatureMk
MythicalCreature.mk (large : Bool) : MythicalCreature
```
同様に、コンストラクタから実際にフィールドを取り出す{anchorName MythicalCreatureLarge}`MythicalCreature.large`関数が作られる。
```anchor MythicalCreatureLarge
#check MythicalCreature.large
```
```anchorInfo MythicalCreatureLarge
MythicalCreature.large (self : MythicalCreature) : Bool
```

古い物語のほとんどでは、どの怪物も何らかの方法で倒せる。
怪物の記述には、それが大きいかどうかに加えてこの情報も含めるべきである。

```anchor Monster
structure Monster extends MythicalCreature where
  vulnerability : String
deriving Repr
```
見出しの{anchorTerm Monster}`extends MythicalCreature`は、どの怪物も伝説の生き物でもあることを述べている。
{anchorName Monster}`Monster`を定義するには、{anchorName Monster}`MythicalCreature`のフィールドと{anchorName Monster}`Monster`のフィールドの両方を与える。
トロールは日光に弱い大きな怪物である。

```anchor troll
def troll : Monster where
  large := true
  vulnerability := "sunlight"
```

裏では、継承は合成を使って実装されている。
{anchorName MonsterMk}`Monster.mk`コンストラクタは{anchorName Monster}`MythicalCreature`を引数に取る。
```anchor MonsterMk
#check Monster.mk
```
```anchorInfo MonsterMk
Monster.mk (toMythicalCreature : MythicalCreature) (vulnerability : String) : Monster
```
新しいフィールドの値を取り出す関数に加えて、型{anchorTerm MonsterToCreature}`Monster → MythicalCreature`の{anchorTerm MonsterToCreature}`Monster.toMythicalCreature`関数が定義される。
これを使うと、その下にある生き物を取り出せる。

Leanで継承の階層を上に移動するのは、オブジェクト指向言語のアップキャストとは同じではない。
アップキャスト演算子は、派生クラスの値を親クラスのインスタンスとして扱わせるが、その値は同一性と構造を保つ。
しかしLeanでは、継承の階層を上に移動すると、その下の情報が実際に消える。
これが実際に起きるのを見るには、{anchorTerm evalTrollCast}`troll.toMythicalCreature`を評価した結果を考えればよい。
```anchor evalTrollCast
#eval troll.toMythicalCreature
```
```anchorInfo evalTrollCast
{ large := true }
```
{anchorName MythicalCreature}`MythicalCreature`のフィールドだけが残る。


{kw}`where`構文と同じく、フィールド名を並べる波括弧の記法も構造体の継承で使える。

```anchor troll2
def troll : Monster := {large := true, vulnerability := "sunlight"}
```
しかし、その下にあるコンストラクタに委ねる無名の山括弧の記法は、内部の細部を明らかにしてしまう。
```anchor wrongTroll1
def troll : Monster := ⟨true, "sunlight"⟩
```
```anchorError wrongTroll1
Application type mismatch: The argument
  true
has type
  Bool
but is expected to have type
  MythicalCreature
in the application
  Monster.mk true
```
山括弧をもう一組付ける必要があり、それによって{anchorName troll3}`true`に{anchorName MythicalCreatureMk}`MythicalCreature.mk`が適用される。

```anchor troll3
def troll : Monster := ⟨⟨true⟩, "sunlight"⟩
```


Leanのドット記法は継承を考慮できる。
言い換えれば、既存の{anchorName trollLargeNoDot}`MythicalCreature.large`を{anchorName Monster}`Monster`に対して使え、Leanが{anchorName trollLargeNoDot}`MythicalCreature.large`の呼び出しの前に{anchorTerm MonsterToCreature}`Monster.toMythicalCreature`の呼び出しを自動で挿入する。
ただしこれが起きるのはドット記法を使うときだけで、フィールドを取り出す関数を普通の関数呼び出しの構文で適用すると型エラーになる。
```anchor trollLargeNoDot
#eval MythicalCreature.large troll
```
```anchorError trollLargeNoDot
Application type mismatch: The argument
  troll
has type
  Monster
but is expected to have type
  MythicalCreature
in the application
  MythicalCreature.large troll
```
ドット記法は、利用者が定義した関数についても継承を考慮できる。
小さな生き物とは、大きくない生き物である。

```anchor small
def MythicalCreature.small (c : MythicalCreature) : Bool := !c.large
```
{anchorTerm smallTroll}`troll.small`を評価すると{anchorTerm smallTroll}`false`になり、{anchorTerm smallTrollWrong}`MythicalCreature.small troll`を評価しようとすると次のようになる。
```anchorError smallTrollWrong
Application type mismatch: The argument
  troll
has type
  Monster
but is expected to have type
  MythicalCreature
in the application
  MythicalCreature.small troll
```

# 多重継承
%%%
tag := "multiple-structure-inheritance"
%%%

助力者は、正しい報酬を与えれば助けてくれる伝説の生き物である。

```anchor Helper
structure Helper extends MythicalCreature where
  assistance : String
  payment : String
deriving Repr
```
たとえば*ニッセ*は小さな妖精の一種で、おいしい粥を与えると家の仕事を手伝うことで知られている。

```anchor elf
def nisse : Helper where
  large := false
  assistance := "household tasks"
  payment := "porridge"
```

家畜化すれば、トロールは優れた助力者になる。
一晩で畑全体を耕せるほど力が強いが、自分の境遇に満足させるにはおもちゃの山羊が要る。
怪物の助手は、助力者でもある怪物である。

```anchor MonstrousAssistant
structure MonstrousAssistant extends Monster, Helper where
deriving Repr
```
この構造体型の値には、両方の親構造体のフィールドをすべて埋める必要がある。

```anchor domesticatedTroll
def domesticatedTroll : MonstrousAssistant where
  large := true
  assistance := "heavy labor"
  payment := "toy goats"
  vulnerability := "sunlight"
```

どちらの親構造体型も{anchorName MythicalCreature}`MythicalCreature`を継承している。
多重継承を素朴に実装すると、「菱形問題」が起きうる。ある{anchorName MonstrousAssistant}`MonstrousAssistant`から{anchorName MythicalCreature}`large`へのどの経路をたどるべきかが分からなくなるのである。
中に入っている{anchorName Monster}`Monster`から{lit}`large`を取るべきか、それとも{anchorName Helper}`Helper`から取るべきか。
Leanでの答えは、祖父母にあたる構造体への最初に指定された経路をたどる、というものである。新しい構造体が両方の親を直接含むのではなく、追加の親構造体のフィールドは複製される。

これは{anchorName MonstrousAssistant}`MonstrousAssistant`のコンストラクタのシグネチャを見れば分かる。
```anchor checkMonstrousAssistantMk
#check MonstrousAssistant.mk
```
```anchorInfo checkMonstrousAssistantMk
MonstrousAssistant.mk (toMonster : Monster) (assistance payment : String) : MonstrousAssistant
```
{anchorName Monster}`Monster`を引数に取り、それに加えて{anchorName Helper}`Helper`が{anchorName MythicalCreature}`MythicalCreature`の上に加える二つのフィールドを取る。
同様に、{anchorName MonstrousAssistantMore}`MonstrousAssistant.toMonster`はコンストラクタから{anchorName Monster}`Monster`を取り出すだけだが、{anchorName printMonstrousAssistantToHelper}`MonstrousAssistant.toHelper`には取り出すべき{anchorName Helper}`Helper`がない。
{kw}`#print`コマンドがその実装を明かす。
```anchor printMonstrousAssistantToHelper
#print MonstrousAssistant.toHelper
```
```anchorInfo printMonstrousAssistantToHelper
@[reducible] def MonstrousAssistant.toHelper : MonstrousAssistant → Helper :=
fun self => { toMythicalCreature := self.toMythicalCreature, assistance := self.assistance, payment := self.payment }
```
この関数は{anchorName MonstrousAssistant}`MonstrousAssistant`のフィールドから{anchorName Helper}`Helper`を組み立てる。
{lit}`@[reducible]`属性は{kw}`abbrev`と書くのと同じ効果がある。

## 既定の宣言
%%%
tag := "inheritance-defaults"
%%%

ある構造体が別の構造体を継承するとき、既定のフィールド定義を使えば、子構造体のフィールドに基づいて親構造体のフィールドを埋められる。
生き物が大きいかどうかより細かい大きさの区別が要るなら、大きさを記述する専用のデータ型を継承と組み合わせて使える。そうすると{anchorName MythicalCreature}`large`フィールドが{anchorName SizedCreature}`size`フィールドの中身から計算される構造体になる。

```anchor SizedCreature
inductive Size where
  | small
  | medium
  | large
deriving BEq

structure SizedCreature extends MythicalCreature where
  size : Size
  large := size == Size.large
```
しかしこの既定の定義はあくまで既定の定義である。
C#やScalaのような言語のプロパティの継承と違い、子構造体の定義が使われるのは{anchorName MythicalCreature}`large`に具体的な値が与えられていないときだけであり、意味の通らない結果も起こりうる。

```anchor nonsenseCreature
def nonsenseCreature : SizedCreature where
  large := false
  size := .large
```
子構造体が親構造体から外れてはならないなら、いくつかの選択肢がある。

 1. {anchorName SizedCreature}`BEq`と{anchorName MonstrousAssistantMore}`Hashable`で行っているように、関係を文書化する。
 2. フィールドが適切に関係しているという命題を定義し、必要な場面でその命題が真である証拠を要求するようにAPIを設計する。
 3. 継承をまったく使わない。

二つ目の選択肢は次のようになる。

```anchor sizesMatch
abbrev SizesMatch (sc : SizedCreature) : Prop :=
  sc.large = (sc.size == Size.large)
```
等号を一つ書くのは*命題*としての等しさを表し、等号を二つ書くのは等しさを調べて{anchorName MythicalCreature}`Bool`を返す関数を表すことに注意せよ。
{anchorName sizesMatch}`SizesMatch`は{kw}`abbrev`として定義されている。証明の中で自動的に展開され、{tactic}`decide`が証明すべき等しさを見られるようにするためである。

*フルドラ*は中くらいの大きさの伝説の生き物である。実際、人間と同じ大きさである。
{anchorName huldresize}`huldre`の二つの大きさのフィールドは互いに一致する。

```anchor huldresize
def huldre : SizedCreature where
  size := .medium

example : SizesMatch huldre := by
  decide
```


## 型クラスの継承
%%%
tag := "type-class-inheritance"
%%%

裏では、型クラスは構造体である。
新しい型クラスを定義すると新しい構造体が定義され、インスタンスを定義するとその構造体型の値が作られる。
そしてそれらはLeanの内部の表に加えられ、要求に応じてインスタンスを見つけられるようにする。
その結果、型クラスは他の型クラスを継承できる。

まったく同じ言語機能を使うので、型クラスの継承は構造体の継承の機能をすべて備える。多重継承、親の型のメソッドの既定の実装、菱形の自動的なつぶし込みなどである。
これは、Java、C#、Kotlinのような言語で複数のインターフェースの継承が役に立つ多くの場面で役に立つ。
型クラスの継承階層を注意深く設計すれば、プログラマは両方の利点を得られる。独立に実装できる細かい抽象の集まりと、より大きく一般的な抽象からそれらの具体的な抽象を自動で組み立てることである。
