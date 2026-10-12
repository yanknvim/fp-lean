module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"

set_option verso.exampleModule "Examples.Props"

set_option pp.rawOnError true

#doc (Manual) "Interlude: Propositions, Proofs, and Indexing" =>
%%%
tag := "props-proofs-indexing"
number := false
htmlSplit := .never
%%%

多くの言語と同じく、Leanでも配列やリストの要素を参照するのに角括弧を使う。
たとえば{moduleTerm}`woodlandCritters`が次のように定義されているとする。

```anchor woodlandCritters
def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]
```

すると個々の要素を取り出せる。

```anchor animals
def hedgehog := woodlandCritters[0]
def deer := woodlandCritters[1]
def snail := woodlandCritters[2]
```

しかし、四番目の要素を取り出そうとすると、実行時エラーではなくコンパイル時のエラーになる。

```anchor outOfBounds
def oops := woodlandCritters[3]
```

```anchorError outOfBounds
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
⊢ 3 < woodlandCritters.length
```

このエラーメッセージは、{moduleTerm}`3 < woodlandCritters.length`（つまり{moduleTerm}`3 < List.length woodlandCritters`）をLeanが自動で数学的に証明しようとした、つまり参照が安全であることを示そうとしたが、できなかった、と言っている。
範囲外参照のエラーはよくある種類の不具合であり、Leanはプログラミング言語と定理証明器という二面性を活かして、できるだけ多くを排除する。

この仕組みを理解するには、命題、証明、タクティクという三つの重要な考え方を理解する必要がある。

# 命題と証明
%%%
tag := "propositions-and-proofs"
%%%

*命題*とは、真にも偽にもなりうる主張である。
次の文はすべて命題である。

 * $`1 + 1 = 2`
 * 加法は可換である。
 * 素数は無限に存在する。
 * $`1 + 1 = 15`
 * パリはフランスの首都である。
 * ブエノスアイレスは韓国の首都である。
 * すべての鳥は飛べる。

一方、意味をなさない文は命題ではない。
次は文法的ではあるが、どれも命題ではない。

 * 1 + green = ice cream
 * すべての首都は素数である。
 * 少なくとも一つのグォーグはフリープである。

命題には二種類ある。概念の定義だけに基づく純粋に数学的な命題と、世界についての事実である命題である。
Leanのような定理証明器が扱うのは前者であり、ペンギンが飛べるかや都市の法的地位については何も言わない。

*証明*とは、ある命題が真であることを納得させる論証である。
数学的な命題では、そうした論証は、関わる概念の定義と論理的な論証の規則を使う。
ほとんどの証明は人が理解するために書かれ、煩雑な細部の多くは省略される。
Leanのような計算機支援の定理証明器は、数学者が細部を省略して証明を書けるように設計されており、省略された明示的な手順を補うのはソフトウェアの役割である。
その手順は機械的に検査できる。
これにより、見落としや誤りの可能性が下がる。

Leanでは、プログラムの型が、そのプログラムとどうやり取りできるかを記述する。
たとえば{moduleTerm}`Nat → List String`型のプログラムは、{moduleTerm}`Nat`の引数を取り、文字列のリストを作る関数である。
言い換えれば、各型は、その型のプログラムとして何が認められるかを定める。

Leanでは、命題は実際に型である。
命題は、その主張が真である証拠として何が認められるかを定める。
この証拠を与えることで命題が証明され、その証拠はLeanが検査する。
一方、命題が偽なら、その証拠を構成することはできない。

たとえば命題$`1 + 1 = 2`はLeanにそのまま書ける。
この命題の証拠はコンストラクタ{moduleTerm}`rfl`であり、*反射律*（reflexivity）の略である。
数学では、すべての要素が自分自身と関係を持つとき、その関係は*反射的*であるという。これは、まともな等しさの概念を持つための基本的な要件である。
{moduleTerm}`1 + 1`は{moduleTerm}`2`に計算されるので、両者は実際に同じものである。

```anchor onePlusOneIsTwo
def onePlusOneIsTwo : 1 + 1 = 2 := rfl
```

一方、{moduleTerm}`rfl`は偽の命題$`1 + 1 = 15`を証明しない。

```anchor onePlusOneIsFifteen
def onePlusOneIsFifteen : 1 + 1 = 15 := rfl
```

```anchorError onePlusOneIsFifteen
Type mismatch
  rfl
has type
  ?m.16 = ?m.16
but is expected to have type
  1 + 1 = 15
```

このエラーメッセージは、等式の両辺がすでに同じ数であるときに、{moduleTerm}`rfl`が二つの式の等しさを証明できることを示している。
{moduleTerm}`1 + 1`は直接{moduleTerm}`2`に評価されるので同じものと見なされ、{moduleTerm}`onePlusOneIsTwo`が受け入れられる。
{moduleTerm}`Type`が、データ構造や関数を表す{moduleTerm}`Nat`、{moduleTerm}`String`、{moduleTerm}`List (Nat × String × (Int → Float))`のような型を記述するのと同じように、{moduleTerm}`Prop`は命題を記述する。

命題が証明されると、それは*定理*と呼ばれる。
Leanでは、定理は{kw}`def`ではなく{kw}`theorem`キーワードで宣言するのが慣例である。
これにより、どの宣言が数学的な証明として読まれるべきもので、どれが定義なのかが読み手に分かりやすい。
一般に、証明では命題が真である証拠があることが重要であり、*どの*証拠が与えられたかはそれほど重要ではない。
一方、定義では、どの具体的な値が選ばれたかが非常に重要である。常に{anchorTerm SomeNats}`0`を返す加法の定義が明らかに誤っていることを思えばよい。
証明の細部は後の証明には関係しないので、{kw}`theorem`キーワードを使うとLeanコンパイラがより並列に処理できる。

先ほどの例は次のように書き直せる。

```anchor onePlusOneIsTwoProp
def OnePlusOneIsTwo : Prop := 1 + 1 = 2

theorem onePlusOneIsTwo : OnePlusOneIsTwo := rfl
```


# タクティク
%%%
tag := "tactics"
%%%

証明は通常、証拠を直接与えるのではなく、*タクティク*を使って書く。
タクティクは、命題の証拠を組み立てる小さなプログラムである。
これらのプログラムは*証明状態*で動き、証明すべき主張（*ゴール*と呼ぶ）と、証明に使える前提を追跡する。
ゴールに対してタクティクを実行すると、新しいゴールを含む新しい証明状態になる。
すべてのゴールが証明されたとき、証明は完了する。

タクティクで証明を書くには、定義を{kw}`by`で始める。
{kw}`by`と書くと、続くインデントされたブロックの終わりまでLeanはタクティクモードになる。
タクティクモードの間、Leanは現在の証明状態について随時フィードバックを返す。
タクティクで書いても、{anchorTerm onePlusOneIsTwoTactics}`onePlusOneIsTwo`はかなり短い。

```anchor onePlusOneIsTwoTactics
theorem onePlusOneIsTwo : 1 + 1 = 2 := by
  decide
```

{tactic}`decide`タクティクは*決定手続き*を呼び出す。決定手続きは、主張が真か偽かを判定し、どちらの場合も適切な証明を返すプログラムである。
主に{anchorTerm SomeNats}`1`や{anchorTerm SomeNats}`2`のような具体的な値を扱うときに使う。
本書で扱う他の重要なタクティクは、「simplify」の略である{tactic}`simp`と、多くの定理を自動で証明できる{tactic}`grind`である。

タクティクが役に立つ理由はいくつかある。
 1. 多くの証明は、細部まで書き下すと複雑で退屈であり、タクティクはそうした面白くない部分を自動化できる。
 2. タクティクで書いた証明は長期的に保守しやすい。柔軟な自動化が、定義の小さな変更を覆い隠してくれるためである。
 3. 一つのタクティクで多くの異なる定理を証明できるので、Leanは舞台裏でタクティクを使い、利用者が手で証明を書かなくて済むようにできる。たとえば配列の参照には添字が範囲内にあることの証明が必要だが、タクティクは通常、利用者が気にしなくてもその証明を組み立ててくれる。

舞台裏では、参照の記法がタクティクを使って、利用者の参照操作が安全であることを証明している。
このタクティクは算術についての多くの事実を考慮し、局所的に分かっている事実と組み合わせて、添字が範囲内にあることを証明しようとする。

{tactic}`simp`タクティクはLeanの証明の働き者である。
ゴールをできるだけ単純な形に書き換える。
多くの場合、この書き換えで主張が自動的に証明できるほど単純になる。
舞台裏では詳細な形式的証明が組み立てられているが、{tactic}`simp`を使うとその複雑さは見えなくなる。

{tactic}`decide`と同じく、{tactic}`grind`タクティクは証明を終わらせるのに使う。
SMTソルバの手法を集めたものを使っており、さまざまな定理を証明できる。
{tactic}`simp`と違い、{tactic}`grind`は証明を完全に終わらせずに途中まで進める、ということがない。完全に成功するか、失敗するかのどちらかである。
{tactic}`grind`は非常に強力で、カスタマイズも拡張もできる。その力と柔軟さのため、証明に失敗したときの出力には多くの情報が含まれ、慣れたLean利用者が失敗の原因を突き止める助けになる。
最初は圧倒されかねないので、この章では{tactic}`decide`と{tactic}`simp`だけを使う。

# 論理結合子
%%%
tag := "connectives"
%%%

「かつ」「または」「真」「偽」「否定」のような論理の基本的な部品を{deftech}*論理結合子*と呼ぶ。
各結合子は、その真理の証拠として何が認められるかを定める。
たとえば「*A*かつ*B*」を証明するには、*A*と*B*の両方を証明しなければならない。
つまり「*A*かつ*B*」の証拠は、*A*の証拠と*B*の証拠の両方を含む組である。
同様に、「*A*または*B*」の証拠は、*A*の証拠か*B*の証拠のどちらかである。

とくに、これらの結合子の多くはデータ型のように定義されており、コンストラクタを持つ。
{anchorTerm AndProp}`A`と{anchorTerm AndProp}`B`が命題なら、「{anchorTerm AndProp}`A`かつ{anchorTerm AndProp}`B`」（{anchorTerm AndProp}`A ∧ B`と書く）も命題である。
{anchorTerm AndProp}`A ∧ B`の証拠はコンストラクタ{anchorTerm AndIntro}`And.intro`であり、その型は{anchorTerm AndIntro}`A → B → A ∧ B`である。
{anchorTerm AndIntro}`A`と{anchorTerm AndIntro}`B`を具体的な命題に置き換えると、{anchorTerm AndIntroEx}`1 + 1 = 2 ∧ "Str".append "ing" = "String"`を{anchorTerm AndIntroEx}`And.intro rfl rfl`で証明できる。
もちろん、{tactic}`decide`もこの証明を見つけられるだけの力がある。

```anchor AndIntroExTac
theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by
  decide
```


同様に、「{anchorTerm OrProp}`A`または{anchorTerm OrProp}`B`」（{anchorTerm OrProp}`A ∨ B`と書く）には二つのコンストラクタがある。「{anchorTerm OrProp}`A`または{anchorTerm OrProp}`B`」の証明には、二つの命題のどちらか一方が真であればよいためである。
コンストラクタは二つある。型{anchorTerm OrIntro1}`A → A ∨ B`を持つ{anchorTerm OrIntro1}`Or.inl`と、型{anchorTerm OrIntro2}`B → A ∨ B`を持つ{anchorTerm OrIntro2}`Or.inr`である。

含意（{anchorTerm impliesDef}`A`なら{anchorTerm impliesDef}`B`）は関数で表す。
とくに、{anchorTerm impliesDef}`A`の証拠を{anchorTerm impliesDef}`B`の証拠に変換する関数が、{anchorTerm impliesDef}`A`が{anchorTerm impliesDef}`B`を含意する証拠そのものである。
これは、{anchorTerm impliesDef}`A → B`が{anchorTerm impliesDef}`¬A ∨ B`の略であるという通常の説明とは違うが、二つの定式化は同等である。

「かつ」の証拠はコンストラクタなので、パターンマッチングに使える。
たとえば、{anchorTerm andImpliesOr}`A`かつ{anchorTerm andImpliesOr}`B`が{anchorTerm andImpliesOr}`A`または{anchorTerm andImpliesOr}`B`を含意する証明は、{anchorTerm andImpliesOr}`A`と{anchorTerm andImpliesOr}`B`の証拠から{anchorTerm andImpliesOr}`A`の証拠（または{anchorTerm andImpliesOr}`B`の証拠）を取り出し、それを使って{anchorTerm andImpliesOr}`A`または{anchorTerm andImpliesOr}`B`の証拠を作る関数である。

```anchor andImpliesOr
theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a b => Or.inl a
```


:::table +header
*
  - 結合子
  - Leanの記法
  - 証拠
*
 -  True
 -  {anchorName connectiveTable}`True`
 -  {anchorTerm connectiveTable}`True.intro : True`

*
 -  False
 -  {anchorName connectiveTable}`False`
 -  証拠なし

*
 -  {anchorName connectiveTable}`A`かつ{anchorName connectiveTable}`B`
 -  {anchorTerm connectiveTable}`A ∧ B`
 -  {anchorTerm connectiveTable}`And.intro : A → B → A ∧ B`

*
 -  {anchorName connectiveTable}`A`または{anchorName connectiveTable}`B`
 -  {anchorTerm connectiveTable}`A ∨ B`
 -  {anchorTerm connectiveTable}`Or.inl : A → A ∨ B`か{anchorTerm connectiveTable}`Or.inr : B → A ∨ B`のどちらか

*
 -  {anchorName connectiveTable}`A`が{anchorName connectiveTable}`B`を含意する
 -  {anchorTerm connectiveTable}`A → B`
 -  {anchorName connectiveTable}`A`の証拠を{anchorName connectiveTable}`B`の証拠に変換する関数

*
 -  {anchorName connectiveTable}`A`の否定
 -  {anchorTerm connectiveTable}`¬A`
 -  {anchorName connectiveTable}`A`の証拠を{anchorName connectiveTable}`False`の証拠に変換するはずの関数


:::

{tactic}`decide`タクティクは、これらの結合子を使った定理も証明できる。
たとえば、

```anchor connectivesD
theorem onePlusOneOrLessThan : 1 + 1 = 2 ∨ 3 < 5 := by decide
theorem notTwoEqualFive : ¬(1 + 1 = 5) := by decide
theorem trueIsTrue : True := by decide
theorem trueOrFalse : True ∨ False := by decide
theorem falseImpliesTrue : False → True := by decide
```


# 証拠を引数にする
%%%
tag := "evidence-passing"
%%%

リストから安全に要素を取り出すには、リストがある大きさ以上である必要があるのに、リスト自体が具体的な値ではなく変数である場合がある。
この参照を安全にするには、リストが十分長いという証拠が要る。
安全な参照を実現する最も簡単な方法の一つは、データ構造を参照する関数が、必要な安全性の証拠を引数として受け取ることである。
たとえば、リストの三番目の要素を返す関数は、一般には安全ではない。リストの要素が0個、1個、2個のこともあるからである。

```anchor thirdErr
def third (xs : List α) : α := xs[2]
```

```anchorError thirdErr
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.5379
xs : List α
⊢ 2 < xs.length
```

しかし、参照操作が安全である証拠を引数として加えれば、リストの要素が少なくとも三つあることを示す義務を呼び出し側に負わせられる。

```anchor third
def third (xs : List α) (ok : xs.length > 2) : α := xs[2]
```

この例の{anchorTerm third}`xs.length > 2`は、{anchorTerm third}`xs`の要素が2個より多いかどうかを調べるプログラムではない。
真にも偽にもなりうる命題であり、引数{anchorTerm third}`ok`はそれが真である証拠でなければならない。

具体的なリストに対して関数を呼ぶ場合、その長さは分かっている。
そのような場合は、{anchorTerm thirdCritters}`by decide`が証拠を自動で組み立てられる。

```anchor thirdCritters
#eval third woodlandCritters (by decide)
```

```anchorInfo thirdCritters
"snail"
```


# 証拠なしの参照
%%%
tag := "indexing-without-evidence"
%%%

参照操作が範囲内にあることを証明するのが現実的でない場合には、別の選択肢がある。
疑問符を付けると{anchorName thirdOption}`Option`になり、添字が範囲内なら{anchorName OptionNames}`some`、そうでなければ{anchorName OptionNames}`none`になる。
たとえば、


```anchor thirdOption
def thirdOption (xs : List α) : Option α := xs[2]?
```

```anchor thirdOptionCritters
#eval thirdOption woodlandCritters
```

```anchorInfo thirdOptionCritters
some "snail"
```

```anchor thirdOptionTwo
#eval thirdOption ["only", "two"]
```

```anchorInfo thirdOptionTwo
none
```

:::paragraph
添字が範囲外のときに{moduleTerm}`Option`を返すのではなく、プログラムをクラッシュさせる版もある。

```anchor crittersBang
#eval woodlandCritters[1]!
```

```anchorInfo crittersBang
"deer"
```
:::


# 出会うかもしれないメッセージ
%%%
tag := "props-proofs-indexing-messages"
%%%
{anchorTerm thirdRabbitErr}`decide`タクティクは、主張が真であることの証明だけでなく、偽であることの証明もできる。
要素が一つのリストが二つより多くの要素を持つことを証明しようとすると、その主張が実際に偽であることを示すエラーを返す。

```anchor thirdRabbitErr
#eval third ["rabbit"] (by decide)
```


```anchorError thirdRabbitErr
Tactic `decide` proved that the proposition
  ["rabbit"].length > 2
is false
```


{tactic}`simp`と{tactic}`decide`のタクティクは、{kw}`def`による定義を自動では展開しない。
{anchorTerm onePlusOneIsStillTwo}`OnePlusOneIsTwo`を{anchorTerm onePlusOneIsStillTwo}`simp`で証明しようとすると失敗する。

```anchor onePlusOneIsStillTwo
theorem onePlusOneIsStillTwo : OnePlusOneIsTwo := by simp
```

エラーメッセージは、何もできなかったとだけ述べている。{anchorTerm onePlusOneIsStillTwo}`OnePlusOneIsTwo`を展開しなければ先に進めないためである。

```anchorError onePlusOneIsStillTwo
`simp` made no progress
```

{anchorTerm onePlusOneIsStillTwo2}`decide`を使っても失敗する。

```anchor onePlusOneIsStillTwo2
theorem onePlusOneIsStillTwo : OnePlusOneIsTwo := by decide
```

これも{anchorName onePlusOneIsStillTwo2}`OnePlusOneIsTwo`を展開しないためである。

```anchorError onePlusOneIsStillTwo2
failed to synthesize
  Decidable OnePlusOneIsTwo

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

{anchorName onePlusOneIsStillTwo}`OnePlusOneIsTwo`を{ref "abbrev-vs-def"}[{kw}`abbrev`で定義し直すと解決する]。展開する対象として印が付けられるからである。

参照操作が安全である証拠をLeanがコンパイル時に見つけられないときのエラーとは別に、安全でない参照を使う多相関数では次のメッセージが出ることがある。

```anchor unsafeThird
def unsafeThird (xs : List α) : α := xs[2]!
```


```anchorError unsafeThird
failed to synthesize instance of type class
  Inhabited α

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

これは、Leanを定理証明のための論理としてもプログラミング言語としても使えるようにしておくための、技術的な制限によるものである。
とくに、クラッシュを許されるのは、型が少なくとも一つの値を持つプログラムだけである。
Leanの命題は、その真理の証拠を分類する一種の型だからである。
偽の命題にはそのような証拠がない。
空の型を持つプログラムがクラッシュできると、そのクラッシュするプログラムが偽の命題の偽の証拠として使えてしまう。

Leanの内部には、少なくとも一つの値を持つことが分かっている型の表がある。
このエラーは、任意の型{anchorTerm unsafeThird}`α`がその表に必ずあるとは限らない、と言っている。
この表に項目を追加する方法と、{anchorTerm unsafeThird}`unsafeThird`のような関数を正しく書く方法は次の章で説明する。

リストと参照用の角括弧の間に空白を入れると、別のメッセージが出ることがある。

```anchor extraSpace
#eval woodlandCritters [1]
```


```anchorError extraSpace
Function expected at
  woodlandCritters
but this term has type
  List String

Note: Expected a function because this term is being applied to the argument
  [1]
```

空白を入れると、Leanはその式を関数適用として扱い、添字を数値を一つだけ含むリストとみなす。
このエラーメッセージは、Leanが{anchorTerm woodlandCritters}`woodlandCritters`を関数として扱おうとした結果である。

## 練習問題
%%%
tag := "props-proofs-indexing-exercises"
%%%

* 次の定理を{anchorTerm exercises}`rfl`で証明せよ。{anchorTerm exercises}`2 + 3 = 5`、{anchorTerm exercises}`15 - 8 = 7`、{anchorTerm exercises}`"Hello, ".append "world" = "Hello, world"`。{anchorTerm exercises}`5 < 18`を{anchorTerm exercises}`rfl`で証明しようとするとどうなるか。その理由は何か。
* 次の定理を{anchorTerm exercises}`by decide`で証明せよ。{anchorTerm exercises}`2 + 3 = 5`、{anchorTerm exercises}`15 - 8 = 7`、{anchorTerm exercises}`"Hello, ".append "world" = "Hello, world"`、{anchorTerm exercises}`5 < 18`。
* リストの五番目の要素を参照する関数を書け。その参照が安全である証拠を引数として渡すようにする。
