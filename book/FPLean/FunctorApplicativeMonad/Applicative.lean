module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.FunctorApplicativeMonad"

#doc (Manual) "Applicative Functors" =>
%%%
tag := "applicative"
%%%

*アプリカティブファンクタ*は、使える操作が二つ増えたファンクタである。{anchorName ApplicativeOption}`pure`と{anchorName ApplicativeOption}`seq`である。
{anchorName ApplicativeOption}`pure`は{anchorName ApplicativeLaws}`Monad`で使うのと同じ演算子である。実際、{anchorName ApplicativeLaws}`Monad`は{anchorName ApplicativeOption}`Applicative`を継承しているためである。
{anchorName ApplicativeOption}`seq`は{anchorName FunctorNames}`map`とよく似ており、データ型の中身を変換するのに関数を使える。
しかし{anchorName ApplicativeOption}`seq`では、関数自体がデータ型の中に入っている。{anchorTerm seqType}`f (α → β) → (Unit → f α) → f β`である。
関数が型{anchorName seqType}`f`の下にあることで、{anchorName ApplicativeOption}`Applicative`インスタンスが関数の適用のしかたを制御できる。一方{anchorName FunctorNames}`Functor.map`は無条件に関数を適用する。
二つ目の引数の型が{anchorTerm seqType}`Unit →`で始まるのは、関数が決して適用されない場合に{anchorName ApplicativeOption}`seq`の定義が途中で打ち切れるようにするためである。

この途中で打ち切る振る舞いの価値は、{anchorTerm ApplicativeOption}`Applicative Option`のインスタンスに見られる。

```anchor ApplicativeOption
instance : Applicative Option where
  pure x := .some x
  seq f x :=
    match f with
    | none => none
    | some g => g <$> x ()
```
この場合、{anchorName ApplicativeOption}`seq`が適用すべき関数がなければ、その引数を計算する必要がないので、{anchorName ApplicativeOption}`x`は決して呼ばれない。
同じ配慮が{anchorName ApplicativeExcept}`Except`の{anchorName ApplicativeExcept}`Applicative`インスタンスにも当てはまる。

```anchor ApplicativeExcept
instance : Applicative (Except ε) where
  pure x := .ok x
  seq f x :=
    match f with
    | .error e => .error e
    | .ok g => g <$> x ()
```
この途中で打ち切る振る舞いは、関数自体ではなく、関数を*包んでいる*{anchorName AlternativeOption}`Option`や{anchorName ApplicativeExcept}`Except`の構造だけに依存する。

モナドは、文を順に実行するという考え方を純粋な関数型言語に取り込む手段と見なせる。
ある文の結果が、次にどの文を実行するかに影響しうる。
これは{anchorName bindType}`bind`の型{anchorTerm bindType}`m α → (α → m β) → m β`に見られる。
一つ目の文の結果の値が、次に実行する文を計算する関数の入力になる。
{anchorName bindType}`bind`を続けて使うのは命令型プログラミング言語の文の並びのようなもので、{anchorName bindType}`bind`は条件分岐やループのような制御構造を実装できるだけの力がある。

この類推に従えば、{anchorName ApplicativeId}`Applicative`は副作用のある言語での関数適用をとらえている。
KotlinやC#のような言語では、関数の引数は左から右へ評価される。
前の引数が行う副作用は、後の引数が行う副作用より先に起きる。
しかし、引数の具体的な*値*に依存する独自の途中打ち切りの演算子を実装するには、関数では力が足りない。

ふつう{anchorName ApplicativeExtendsFunctorOne}`seq`を直接呼び出すことはない。
代わりに{lit}`<*>`演算子を使う。
この演算子は二つ目の引数を{lit}`fun () => ...`で包み、呼び出し側を簡単にする。
言い換えれば、{anchorTerm seqSugar}`E1 <*> E2`は{anchorTerm seqSugar}`Seq.seq E1 (fun () => E2)`の糖衣構文である。


{anchorName ApplicativeExtendsFunctorOne}`seq`を複数の引数で使えるようにする鍵は、Leanの複数引数の関数が実際には一引数の関数で、残りの引数を待つ別の関数を返すことである。
言い換えれば、{anchorName ApplicativeExtendsFunctorOne}`seq`の一つ目の引数が複数の引数を待っているなら、その{anchorName ApplicativeExtendsFunctorOne}`seq`の結果は残りを待つことになる。
たとえば{anchorTerm somePlus}`some Plus.plus`は型{anchorTerm somePlus}`Option (Nat → Nat → Nat)`を持てる。
引数を一つ与えた{anchorTerm somePlusFour}`some Plus.plus <*> some 4`は型{anchorTerm somePlusFour}`Option (Nat → Nat)`になる。
これ自体も{anchorName ApplicativeExtendsFunctorOne}`seq`で使えるので、{anchorTerm somePlusFourSeven}`some Plus.plus <*> some 4 <*> some 7`は型{anchorTerm somePlusFourSeven}`Option Nat`を持つ。

すべてのファンクタがアプリカティブなわけではない。
{anchorName Pair}`Pair`は組み込みの直積型{anchorName names}`Prod`のようなものである。

```anchor Pair
structure Pair (α β : Type) : Type where
  first : α
  second : β
```
{anchorName ApplicativeExcept}`Except`と同じく、{anchorTerm PairType}`Pair`の型は{anchorTerm PairType}`Type → Type → Type`である。
つまり{anchorTerm FunctorPair}`Pair α`の型は{anchorTerm PairType}`Type → Type`であり、{anchorName FunctorPair}`Functor`インスタンスが可能である。

```anchor FunctorPair
instance : Functor (Pair α) where
  map f x := ⟨x.first, f x.second⟩
```
このインスタンスは{anchorName FunctorPair}`Functor`の契約を満たす。

確かめるべき性質は二つある。{anchorEvalStep checkPairMapId 0}`id <$> Pair.mk x y`{lit}` = `{anchorEvalStep checkPairMapId 2}`Pair.mk x y`と、{anchorEvalStep checkPairMapComp1 0}`f <$> g <$> Pair.mk x y`{lit}` = `{anchorEvalStep checkPairMapComp2 0}`(f ∘ g) <$> Pair.mk x y`である。
一つ目の性質は、左辺の評価を一段ずつたどり、右辺に評価されることに気づけば確かめられる。
```anchorEvalSteps checkPairMapId
id <$> Pair.mk x y
===>
Pair.mk x (id y)
===>
Pair.mk x y
```
二つ目は、両辺を一段ずつたどり、同じ結果になることを見れば確かめられる。
```anchorEvalSteps checkPairMapComp1
f <$> g <$> Pair.mk x y
===>
f <$> Pair.mk x (g y)
===>
Pair.mk x (f (g y))
```
```anchorEvalSteps checkPairMapComp2
(f ∘ g) <$> Pair.mk x y
===>
Pair.mk x ((f ∘ g) y)
===>
Pair.mk x (f (g y))
```

しかし、{anchorName ApplicativeExcept}`Applicative`インスタンスを定義しようとすると、うまくいかない。
{anchorName Pairpure (show := pure)}`Pair.pure`の定義が要る。
```anchor Pairpure
def Pair.pure (x : β) : Pair α β := _
```
```anchorError Pairpure
don't know how to synthesize placeholder
context:
β α : Type
x : β
⊢ Pair α β
```
型{anchorName Pairpure2}`β`の値（つまり{anchorName Pairpure2}`x`）は使えるので、アンダースコアのエラーメッセージは、次の段階がコンストラクタ{anchorName Pairpure2}`Pair.mk`を使うことだと示唆している。
```anchor Pairpure2
def Pair.pure (x : β) : Pair α β := Pair.mk _ x
```
```anchorError Pairpure2
don't know how to synthesize placeholder for argument `first`
context:
β α : Type
x : β
⊢ α
```
残念ながら、使える{anchorName Pairpure2}`α`がない。
{anchorTerm ApplicativePair}`Applicative (Pair α)`のインスタンスを定義するには、{anchorName Pairpure2 (show := pure)}`Pair.pure`が*考えられるすべての型*{anchorName Pairpure2}`α`で働く必要があるので、これは不可能である。
何しろ、呼び出し側は{anchorName Pairpure2}`α`として、値がまったくない{anchorName ApplicativePair}`Empty`を選ぶこともできる。

# モナドでないアプリカティブ
%%%
tag := "validate"
%%%

フォームへの利用者の入力を検査するときは、エラーを一度に一つずつ出すより、まとめて多数出すのがよいと一般に考えられている。
そうすれば利用者は、エラーを欄ごとに直しながら責められている気になるより、コンピュータを満足させるのに何が必要かを全体として見渡せる。

理想的には、利用者の入力の検査は、その検査を行う関数の型に見えるべきである。
返すデータ型は具体的であるべきである。たとえば、テキスト欄に数が入っているかを検査するなら、実際の数の型を返すべきである。
検査の手続きは、入力が検査を通らないときに例外を投げることもできる。
しかし例外には大きな欠点がある。最初のエラーでプログラムが終わってしまい、エラーの一覧を蓄積できない。

一方、エラーの一覧を蓄積し、それが空でないときに失敗するというよくある設計も問題がある。
入力データの各部分を検査する{kw}`if`文が長く入れ子になると保守しにくく、エラーメッセージを一つ二つ見落とすのもたやすい。
理想的には、新しい値を返せるようにしつつ、エラーメッセージを自動で追跡して蓄積するAPIを使って検査を行える。

{anchorName Validate}`Validate`というアプリカティブファンクタが、この形のAPIを実装する一つの方法を与える。
{anchorName ApplicativeExcept}`Except`モナドと同じく、{anchorName Validate}`Validate`は、検査済みのデータを正確にとらえた新しい値を組み立てられるようにする。
{anchorName ApplicativeExcept}`Except`と違い、複数のエラーを蓄積でき、一覧が空かどうかを調べ忘れる心配もない。

## 利用者の入力
%%%
tag := "user-input"
%%%
利用者の入力の例として、次の構造体を考えよう。

```anchor RawInput
structure RawInput where
  name : String
  birthYear : String
```
実装すべき業務の規則は次のとおりである。
 1. 名前は空であってはならない。
 2. 生年は数値で、負であってはならない。
 3. 生年は1900より大きく、そのフォームを検査する年以下でなければならない。

これらをデータ型として表すには、*部分型*と呼ばれる新しい機能が要る。
この道具があれば、アプリカティブファンクタでエラーを追跡する検査の枠組みを書けるようになり、これらの規則をその枠組みの中で実装できる。

## 部分型
%%%
tag := "subtypes"
%%%

これらの条件を表すには、{anchorName Subtype}`Subtype`というLeanの型をもう一つ使うのが最も簡単である。

```anchor Subtype
structure Subtype {α : Type} (p : α → Prop) where
  val : α
  property : p val
```
この構造体には型引数が二つある。データの型{anchorName Subtype}`α`である暗黙の引数と、{anchorName Subtype}`α`上の述語である明示的な引数{anchorName Subtype}`p`である。
*述語*とは、変数を含む論理的な言明で、その変数を値に置き換えると実際の言明になるもののことである。参照で添字が範囲内にあるとはどういうことかを記述する{ref "overloading-indexing"}[{moduleName}`GetElem`の引数]のようなものである。
{anchorName Subtype}`Subtype`の場合、その述語は{anchorName Subtype}`α`の値のうち述語が成り立つ部分集合を切り出す。
この構造体の二つのフィールドは、それぞれ{anchorName Subtype}`α`の値と、その値が述語{anchorName Subtype}`p`を満たす証拠である。
Leanには{anchorName Subtype}`Subtype`のための特別な構文がある。
{anchorName Subtype}`p`の型が{anchorTerm Subtype}`α → Prop`なら、型{anchorTerm subtypeSugarIn}`Subtype p`は{anchorTerm subtypeSugar}`{x : α // p x}`とも書ける。型{anchorName Subtype}`α`が自動で推論できるときは{anchorTerm subtypeSugar2}`{x // p x}`とも書ける。

{ref "positive-numbers"}[正の数を帰納型として表す]方法は明快で、プログラミングしやすい。
しかし、大きな欠点がある。
{anchorName names}`Nat`と{anchorName names}`Int`は、Leanのプログラムから見れば普通の帰納型の構造を持つが、コンパイラはこれらを特別に扱い、高速な任意精度数のライブラリで実装している。
利用者が定義した型ではそうならない。
しかし、{anchorName names}`Nat`の部分型として0でない数に制限すれば、新しい型が効率のよい表現を使いつつ、コンパイル時に0を排除できる。

```anchor FastPos
def FastPos : Type := {x : Nat // x > 0}
```

最小の高速な正の数もやはり1である。
今度は、帰納型のコンストラクタではなく、山括弧で組み立てる構造体の値である。
一つ目の引数はその下にある{anchorName FastPos}`Nat`であり、二つ目の引数はその{anchorName FastPos}`Nat`が0より大きいという証拠である。

```anchor one
def one : FastPos := ⟨1, by decide⟩
```
命題{anchorTerm onep}`1 > 0`は決定可能なので、{tactic}`decide`タクティクが必要な証拠を作る。
{anchorName OfNatFastPos}`OfNat`インスタンスは{anchorName Pos (module:=Examples.Classes)}`Pos`のものとよく似ているが、{lit}`n + 1 > 0`の証拠を与えるのに短いタクティクの証明を使う点が異なる。

```anchor OfNatFastPos
instance : OfNat FastPos (n + 1) where
  ofNat := ⟨n + 1, by simp⟩
```
ここで{tactic}`simp`が要るのは、{tactic}`decide`が具体的な値を必要とするのに、問題の命題が{anchorTerm OfNatFastPosp}`n + 1 > 0`だからである。

部分型はもろ刃の剣である。
検査の規則を効率よく表せるが、それらの規則を保つ負担をライブラリの利用者に移すことになる。利用者は、重要な不変条件を破っていないことを*証明*せねばならない。
一般には、ライブラリの内部で使うのがよく、利用者にはすべての不変条件が満たされることを自動で保証するAPIを提供し、必要な証明はライブラリの内部に収めるのがよい。

型{anchorName NatFastPosRemarks}`α`の値が部分型{anchorTerm NatFastPosRemarks}`{x : α // p x}`に入っているかを調べるには、通常、命題{anchorTerm NatFastPosRemarks}`p x`が決定可能である必要がある。
{ref "equality-and-ordering"}[等価性と順序のクラスの節]で、決定可能な命題を{kw}`if`でどう使えるかを述べた。
決定可能な命題とともに{kw}`if`を使うときは、名前を付けられる。
{kw}`then`の枝ではその名前に命題が真である証拠が束縛され、{kw}`else`の枝では偽である証拠が束縛される。
これは、与えられた{anchorName NatFastPos}`Nat`が正かどうかを調べるときに役に立つ。

```anchor NatFastPos
def Nat.asFastPos? (n : Nat) : Option FastPos :=
  if h : n > 0 then
    some ⟨n, h⟩
  else none
```
{kw}`then`の枝では{anchorName NatFastPos}`h`に{anchorTerm NatFastPos}`n > 0`の証拠が束縛され、この証拠を{anchorName Subtype}`Subtype`のコンストラクタの二つ目の引数として使える。


## 検査済みの入力
%%%
tag := "validated-input"
%%%

検査済みの利用者の入力は、複数の技法を使って業務の規則を表す構造体である。
 * 構造体の型自体が、妥当性を検査した年を符号化しているので、{anchorTerm CheckedInputEx}`CheckedInput 2019`と{anchorTerm CheckedInputEx}`CheckedInput 2020`は同じ型ではない。
 * 生年は{anchorName CheckedInput}`String`ではなく{anchorName CheckedInput}`Nat`で表す。
 * 部分型を使って、名前と生年のフィールドで許される値を制限する。

```anchor CheckedInput
structure CheckedInput (thisYear : Nat) : Type where
  name : {n : String // n ≠ ""}
  birthYear : {y : Nat // y > 1900 ∧ y ≤ thisYear}
```

:::paragraph
入力の検査器は、現在の年と{anchorName RawInput}`RawInput`を引数に取り、検査済みの入力か、少なくとも一つの検査の失敗を返すべきである。
これは{anchorName Validate}`Validate`型で表す。
```anchor Validate
inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α
```
{anchorName ApplicativeExcept}`Except`とよく似ている。
唯一の違いは、{anchorName Validate}`errors`コンストラクタが複数の失敗を含みうることである。
:::

{anchorName Validate}`Validate`はファンクタである。
関数をマップすると、あるかもしれない成功の値が変換される。{anchorName ApplicativeExcept}`Except`の{anchorName FunctorValidate}`Functor`インスタンスと同じである。

```anchor FunctorValidate
instance : Functor (Validate ε) where
  map f
   | .ok x => .ok (f x)
   | .errors errs => .errors errs
```

{anchorName ApplicativeValidate}`Validate`の{anchorName ApplicativeValidate}`Applicative`インスタンスは{anchorName ApplicativeExcept}`Except`のインスタンスと重要な違いがある。{anchorName ApplicativeExcept}`Except`のインスタンスは最初に出会ったエラーで終わるが、{anchorName ApplicativeValidate}`Validate`のインスタンスは、関数と引数の*両方*の枝からエラーをすべて蓄積するようにしている。

```anchor ApplicativeValidate
instance : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => g <$> (x ())
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')
```

:::paragraph
{anchorName ApplicativeValidate}`.errors`を{anchorName Validate}`NonEmptyList`のコンストラクタと一緒に使うのは少し冗長である。
{anchorName reportError}`reportError`のような補助関数があるとコードが読みやすくなる。
この用途では、エラーの報告はフィールド名とメッセージの組にする。

```anchor Field
def Field := String
```

```anchor reportError
def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors { head := (f, msg), tail := [] }
```
:::

{anchorName ApplicativeValidate}`Validate`の{anchorName ApplicativeValidate}`Applicative`インスタンスを使うと、各フィールドの検査の手続きを独立に書いてから組み合わせられる。
名前の検査は、文字列が空でないことを確かめ、その事実の証拠を{anchorName Subtype}`Subtype`の形で返すことから成る。
ここでは証拠を束縛する版の{kw}`if`を使う。

```anchor checkName
def checkName (name : String) :
    Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = "" then
    reportError "name" "Required"
  else pure ⟨name, h⟩
```
{kw}`then`の枝では{anchorName checkName}`h`に{anchorTerm checkName}`name = ""`の証拠が束縛され、{kw}`else`の枝では{lit}`¬name = ""`の証拠が束縛される。

検査のエラーの中には、他の検査を不可能にするものもある。
たとえば、戸惑った利用者が数の代わりに{anchorTerm checkDavidSyzygy}`"syzygy"`という語を書いたなら、生年のフィールドが1900より大きいかを調べても意味がない。
数の許される範囲を調べるのは、そのフィールドが実際に数を含むことを確かめた後で初めて意味を持つ。
これは{anchorName ValidateAndThen (show := andThen)}`Validate.andThen`関数で表せる。

```anchor ValidateAndThen
def Validate.andThen (val : Validate ε α)
    (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x => next x
```
この関数の型シグネチャは{anchorTerm bindType}`Monad`インスタンスの{anchorName bindType}`bind`として使うのに適しているが、そうしないのには十分な理由がある。
それらは{ref "additional-stipulations"}[{anchorName ApplicativeExcept}`Applicative`の契約を述べる節]で説明する。

生年が数であるかを調べるには、{anchorTerm CheckedInputEx}`String.Slice.toNat? : String.Slice → Option Nat`という組み込みの関数が役に立つ。
まず{anchorName CheckedInputEx}`String.trimAscii`で前後の空白を取り除くのが最も利用者に親切である。

```anchor checkYearIsNat
def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trimAscii.toNat? with
  | none => reportError "birth year" "Must be digits"
  | some n => pure n
```

:::paragraph
与えられた年が期待される範囲にあるかを調べるには、証拠を与える形の{kw}`if`を入れ子にして使う。

```anchor checkBirthYear
def checkBirthYear (thisYear year : Nat) :
    Validate (Field × String) {y : Nat // y > 1900 ∧ y ≤ thisYear} :=
  if h : year > 1900 then
    if h' : year ≤ thisYear then
      pure ⟨year, by simp [*]⟩
    else reportError "birth year" s!"Must be no later than {thisYear}"
  else reportError "birth year" "Must be after 1900"
```
:::

:::paragraph
最後に、この三つの部分を{anchorTerm checkInput}`<*>`で組み合わせられる。

```anchor checkInput
def checkInput (year : Nat) (input : RawInput) :
    Validate (Field × String) (CheckedInput year) :=
  pure CheckedInput.mk <*>
    checkName input.name <*>
    (checkYearIsNat input.birthYear).andThen fun birthYearAsNat =>
      checkBirthYear year birthYearAsNat
```
:::

:::paragraph
{anchorName checkDavid1984}`checkInput`を試すと、確かに複数の指摘を返せることが分かる。
```anchor checkDavid1984
#eval checkInput 2023 {name := "David", birthYear := "1984"}
```
```anchorInfo checkDavid1984
Validate.ok { name := "David", birthYear := 1984 }
```
```anchor checkBlank2045
#eval checkInput 2023 {name := "", birthYear := "2045"}
```
```anchorInfo checkBlank2045
Validate.errors { head := ("name", "Required"), tail := [("birth year", "Must be no later than 2023")] }
```
```anchor checkDavidSyzygy
#eval checkInput 2023 {name := "David", birthYear := "syzygy"}
```
```anchorInfo checkDavidSyzygy
Validate.errors { head := ("birth year", "Must be digits"), tail := [] }
```
:::

{anchorName checkInput}`checkInput`によるフォームの検査は、{anchorName ApplicativeNames}`Applicative`が{anchorName MonadExtends}`Monad`より優れている要点を示している。
{lit}`>>=`は一つ目の段階の値に基づいてプログラムの残りの実行を変えられるだけの力があるので、渡すべき値を一つ目の段階から*必ず*受け取らねばならない。
値を受け取らなければ（たとえばエラーが起きたため）、{lit}`>>=`はプログラムの残りを実行できない。
{anchorName Validate}`Validate`は、それでもプログラムの残りを実行すると役に立つ場合があることを示している。前のデータが要らない場合には、プログラムの残りを実行すると役に立つ情報（この場合はさらに多くの検査エラー）が得られるのである。
{anchorName ApplicativeNames}`Applicative`の{lit}`<*>`は、結果を組み直す前に両方の引数を実行してよい。
同様に、{lit}`>>=`は逐次的な実行を強いる。
各段階は、次が走る前に完了していなければならない。
これは一般に役に立つが、プログラムの実際のデータ依存関係から自然に現れる、異なるスレッドの並行実行はできなくなる。
{anchorName MonadExtends}`Monad`のようなより強力な抽象は、APIの利用者に与えられる柔軟さを増やすが、APIの実装者に与えられる柔軟さは減らす。
