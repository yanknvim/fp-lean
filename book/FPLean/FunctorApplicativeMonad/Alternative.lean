module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.FunctorApplicativeMonad"

#doc (Manual) "Alternatives" =>
%%%
tag := "alternative"
%%%


# 失敗からの復帰
%%%
tag := "alternative-recovery"
%%%

{anchorName Validate}`Validate`は、入力を受け付けられる方法が複数ある場面でも使える。
入力フォーム{anchorName RawInput}`RawInput`について、旧システムの慣習を実装した別の業務規則は次のようなものになりうる。

 1. 人間の利用者は全員、4桁の生年を提供しなければならない。
 2. 1970年より前に生まれた利用者は、古い記録が不完全なため、名前を提供しなくてよい。
 3. 1970年より後に生まれた利用者は、名前を提供しなければならない。
 4. 企業は生年として{anchorTerm checkCompany}`"FIRM"`を入力し、企業名を提供するべきである。

1970年生まれの利用者については、特に何も定めていない。
彼らは諦めるか、生年を偽るか、電話をかけてくるだろうと想定されている。
企業はこれを、事業を行ううえで受け入れられるコストと考えている。

次の帰納型は、これらの定められた規則から生み出されうる値をとらえている。

```anchor LegacyCheckedInput
abbrev NonEmptyString := {s : String // s ≠ ""}

inductive LegacyCheckedInput where
  | humanBefore1970 :
    (birthYear : {y : Nat // y > 999 ∧ y < 1970}) →
    String →
    LegacyCheckedInput
  | humanAfter1970 :
    (birthYear : {y : Nat // y > 1970}) →
    NonEmptyString →
    LegacyCheckedInput
  | company :
    NonEmptyString →
    LegacyCheckedInput
deriving Repr
```

しかし、これらの規則の検査器は、三つの場合すべてに対応する必要があるので、もっと複雑になる。
入れ子になった{kw}`if`式の並びとして書くこともできるが、三つの場合を独立に設計してから組み合わせるほうが簡単である。
そのためには、エラーメッセージを保ったまま失敗から復帰する手段が要る。

```anchor ValidateorElse
def Validate.orElse
    (a : Validate ε α)
    (b : Unit → Validate ε α) :
    Validate ε α :=
  match a with
  | .ok x => .ok x
  | .errors errs1 =>
    match b () with
    | .ok x => .ok x
    | .errors errs2 => .errors (errs1 ++ errs2)
```

この失敗からの復帰のパターンはよくあるので、Leanには{anchorName OrElse}`OrElse`という型クラスに結び付いた組み込みの構文がある。

```anchor OrElse
class OrElse (α : Type) where
  orElse : α → (Unit → α) → α
```
式{anchorTerm OrElseSugar}`E1 <|> E2`は{anchorTerm OrElseSugar}`OrElse.orElse E1 (fun () => E2)`の略である。
{anchorName Validate}`Validate`の{anchorName OrElse}`OrElse`インスタンスがあれば、この構文をエラーからの復帰に使える。

```anchor OrElseValidate
instance : OrElse (Validate ε α) where
  orElse := Validate.orElse
```

{anchorName LegacyCheckedInput}`LegacyCheckedInput`の検査器は、各コンストラクタの検査器から組み立てられる。
企業の規則は、生年が文字列{anchorTerm checkCompany}`"FIRM"`であるべきことと、名前が空でないべきことを述べている。
しかし、{anchorName names1}`LegacyCheckedInput.company`コンストラクタには生年の表現がまったくないので、{anchorTerm checkCompanyProv}`<*>`を使ってその検査を行う簡単な方法がない。
鍵は、引数を無視する関数を{anchorTerm checkCompanyProv}`<*>`とともに使うことである。

真偽値の条件が成り立つことを、その事実の証拠を型に記録せずに調べるには、{anchorName checkThat}`checkThat`を使う。

```anchor checkThat
def checkThat (condition : Bool)
    (field : Field) (msg : String) :
    Validate (Field × String) Unit :=
  if condition then pure () else reportError field msg
```
この{anchorName checkCompanyProv}`checkCompany`の定義は{anchorName checkCompanyProv}`checkThat`を使い、その結果の{anchorName checkThat}`Unit`の値を捨てる。

```anchor checkCompanyProv
def checkCompany (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  pure (fun () name => .company name) <*>
    checkThat (input.birthYear == "FIRM")
      "birth year" "FIRM if a company" <*>
    checkName input.name
```

しかし、この定義はかなり煩わしい。
二つの方法で簡単にできる。
一つ目は、最初の{anchorTerm checkCompanyProv}`<*>`の使用を、一つ目の引数が返す値を自動で無視する専用の版{anchorTerm checkCompany}`*>`に置き換えることである。
この演算子も{anchorName ClassSeqRight}`SeqRight`という型クラスで制御されており、{anchorTerm seqRightSugar}`E1 *> E2`は{anchorTerm seqRightSugar}`SeqRight.seqRight E1 (fun () => E2)`の糖衣構文である。

```anchor ClassSeqRight
class SeqRight (f : Type → Type) where
  seqRight : f α → (Unit → f β) → f β
```
{anchorName ClassSeqRight}`seqRight`には{anchorName fakeSeq}`seq`を使った既定の実装がある。{lit}`seqRight (a : f α) (b : Unit → f β) : f β := pure (fun _ x => x) <*> a <*> b ()`である。

{anchorName ClassSeqRight}`seqRight`を使うと、{anchorName checkCompanyProv2}`checkCompany`が簡単になる。

```anchor checkCompanyProv2
def checkCompany (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM")
    "birth year" "FIRM if a company" *>
  pure .company <*> checkName input.name
```
もう一段の簡略化ができる。
どの{anchorName ApplicativeExcept}`Applicative`についても、{anchorTerm ApplicativeLaws}`pure f <*> E`は{anchorTerm ApplicativeLaws}`f <$> E`と等しい。
言い換えれば、{anchorName ApplicativeExtendsFunctorOne}`pure`で{anchorName ApplicativeExtendsFunctorOne}`Applicative`の型に入れた関数を適用するのに{anchorName fakeSeq}`seq`を使うのは大げさであり、その関数は{anchorName ApplicativeLaws}`Functor.map`で適用すればよかったのである。
この簡略化により次のようになる。

```anchor checkCompany
def checkCompany (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM")
    "birth year" "FIRM if a company" *>
  .company <$> checkName input.name
```

{anchorName LegacyCheckedInput}`LegacyCheckedInput`の残り二つのコンストラクタは、フィールドに部分型を使う。
部分型を調べる汎用の道具があると、これらが読みやすくなる。

```anchor checkSubtype
def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)]
    (err : ε) : Validate ε {x : α // p x} :=
  if h : p v then
    pure ⟨v, h⟩
  else
    .errors { head := err, tail := [] }
```
この関数の引数の並びでは、型クラス{anchorTerm checkSubtype}`[Decidable (p v)]`が引数{anchorName checkSubtype}`v`と{anchorName checkSubtype}`p`の指定より後に来ることが重要である。
そうでなければ、手で与えた値ではなく、自動の暗黙引数がもう一組あるものを指すことになる。
{anchorName checkSubtype}`Decidable`インスタンスがあることで、命題{anchorTerm checkSubtype}`p v`を{kw}`if`で調べられる。

人間の二つの場合は、追加の道具を必要としない。

```anchor checkHumanBefore1970
def checkHumanBefore1970 (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanBefore1970 <$>
      checkSubtype y (fun x => x > 999 ∧ x < 1970)
        ("birth year", "less than 1970") <*>
      pure input.name
```

```anchor checkHumanAfter1970
def checkHumanAfter1970 (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanAfter1970 <$>
      checkSubtype y (· > 1970)
        ("birth year", "greater than 1970") <*>
      checkName input.name
```

三つの場合の検査器は{anchorTerm OrElseSugar}`<|>`で組み合わせられる。

```anchor checkLegacyInput
def checkLegacyInput (input : RawInput) :
    Validate (Field × String) LegacyCheckedInput :=
  checkCompany input <|>
  checkHumanBefore1970 input <|>
  checkHumanAfter1970 input
```

成功した場合は、予想どおり{anchorName LegacyCheckedInput}`LegacyCheckedInput`のコンストラクタを返す。
```anchor trollGroomers
#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩
```
```anchorInfo trollGroomers
Validate.ok (LegacyCheckedInput.company "Johnny's Troll Groomers")
```
```anchor johnny
#eval checkLegacyInput ⟨"Johnny", "1963"⟩
```
```anchorInfo johnny
Validate.ok (LegacyCheckedInput.humanBefore1970 1963 "Johnny")
```
```anchor johnnyAnon
#eval checkLegacyInput ⟨"", "1963"⟩
```
```anchorInfo johnnyAnon
Validate.ok (LegacyCheckedInput.humanBefore1970 1963 "")
```

最悪の入力は、起こりうる失敗をすべて返す。
```anchor allFailures
#eval checkLegacyInput ⟨"", "1970"⟩
```
```anchorInfo allFailures
Validate.errors
  { head := ("birth year", "FIRM if a company"),
    tail := [("name", "Required"),
             ("birth year", "less than 1970"),
             ("birth year", "greater than 1970"),
             ("name", "Required")] }
```


# {lit}`Alternative`クラス
%%%
tag := "Alternative"
%%%

多くの型が、失敗と復帰という考え方に対応している。
{ref "nondeterministic-search"}[さまざまなモナドで算術式を評価する]節の{anchorName AlternativeMany}`Many`モナドもそうした型の一つであり、{anchorName AlternativeOption}`Option`も同様である。
どちらも理由を示さずに失敗に対応する（たとえば{anchorName ApplicativeExcept}`Except`や{anchorName Validate}`Validate`は、何が問題だったかの示唆を要求するが、それとは違う）。

{anchorName FakeAlternative}`Alternative`クラスは、失敗と復帰のための演算子が増えたアプリカティブファンクタを記述する。

```anchor FakeAlternative
class Alternative (f : Type → Type) extends Applicative f where
  failure : f α
  orElse : f α → (Unit → f α) → f α
```
{anchorTerm misc}`Add α`の実装者が{anchorTerm misc}`HAdd α α α`のインスタンスをただで得るのと同じように、{anchorName FakeAlternative}`Alternative`の実装者は{anchorName OrElse}`OrElse`のインスタンスをただで得る。

```anchor AltOrElse
instance [Alternative f] : OrElse (f α) where
  orElse := Alternative.orElse
```

{anchorName ApplicativeOption}`Option`の{anchorName FakeAlternative}`Alternative`の実装は、{anchorName ApplicativeOption}`none`でない最初の引数を保つ。

```anchor AlternativeOption
instance : Alternative Option where
  failure := none
  orElse
    | some x, _ => some x
    | none, y => y ()
```
同様に、{anchorName AlternativeMany}`Many`の実装は{moduleName (module := Examples.Monads.Many)}`Many.union`の全体的な構造に従うが、遅延を生む{anchorName guard}`Unit`の引数の置き場所が違うため細かな違いがある。

```anchor AlternativeMany
def Many.orElse : Many α → (Unit → Many α) → Many α
  | .none, ys => ys ()
  | .more x xs, ys => .more x (fun () => orElse (xs ()) ys)

instance : Alternative Many where
  failure := .none
  orElse := Many.orElse
```

他の型クラスと同じく、{anchorName FakeAlternative}`Alternative`があれば、{anchorName FakeAlternative}`Alternative`を実装する*どの*アプリカティブファンクタでも働くさまざまな操作を定義できる。
最も重要なものの一つが{anchorName guard}`guard`で、決定可能な命題が偽のときに{anchorName guard}`failure`を起こす。

```anchor guard
def guard [Alternative f] (p : Prop) [Decidable p] : f Unit :=
  if p then
    pure ()
  else failure
```
モナドを使うプログラムでは、実行を早期に終わらせられるととても役に立つ。
{anchorName evenDivisors}`Many`では、探索の枝を丸ごとふるい落とすのに使える。次のプログラムは自然数の偶数である約数をすべて計算する。

```anchor evenDivisors
def Many.countdown : Nat → Many Nat
  | 0 => .none
  | n + 1 => .more n (fun () => countdown n)

def evenDivisors (n : Nat) : Many Nat := do
  let k ← Many.countdown (n + 1)
  guard (k % 2 = 0)
  guard (n % k = 0)
  pure k
```
{anchorTerm evenDivisors20}`20`で実行すると期待どおりの結果になる。
```anchor evenDivisors20
#eval (evenDivisors 20).takeAll
```
```anchorInfo evenDivisors20
[20, 10, 4, 2]
```


# 練習問題
%%%
tag := "Alternative-exercises"
%%%

## 検査の分かりやすさを改善する
%%%
tag := none
%%%

{anchorTerm OrElseSugar}`<|>`を使う{anchorName Validate}`Validate`のプログラムが返すエラーは読みにくいことがある。エラーの一覧に入っているということは、*何らかの*コードの道筋を通ればそのエラーに到達しうる、というだけの意味だからである。
より構造化されたエラーの報告を使えば、利用者をより正確に手順へ導ける。

 * {anchorName misc}`Validate.errors`の{anchorName Validate}`NonEmptyList`を裸の型変数に置き換え、{anchorTerm ApplicativeValidate}`Applicative (Validate ε)`と{anchorTerm OrElseValidate}`OrElse (Validate ε α)`のインスタンスの定義を、{anchorTerm misc}`Append ε`インスタンスがあることだけを要求するように直す。
 * 検査の実行で生じたエラーをすべて変換する関数{anchorTerm misc}`Validate.mapErrors : Validate ε α → (ε → ε') → Validate ε' α`を定義する。
 * エラーを表すのに{anchorName TreeError}`TreeError`データ型を使い、三つの選択肢を通る経路を追跡するように旧システムの検査を書き直す。
 * {anchorName TreeError}`TreeError`が蓄積した警告とエラーを利用者に分かりやすく出力する関数{anchorTerm misc}`report : TreeError → String`を書く。

```anchor TreeError
inductive TreeError where
  | field : Field → String → TreeError
  | path : String → TreeError → TreeError
  | both : TreeError → TreeError → TreeError

instance : Append TreeError where
  append := .both
```
