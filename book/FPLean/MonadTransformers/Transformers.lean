module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.MonadTransformers.Defs"

#doc (Manual) "A Monad Construction Kit" =>

{anchorName m}`ReaderT`は、役に立つモナド変換子のうちの一つにすぎない。
この節では、さらにいくつかの変換子を述べる。
モナド変換子はそれぞれ次のものから成る。
 1. モナドを引数に取る定義かデータ型{anchorName general}`T`。
    その型は{anchorTerm general}`(Type u → Type v) → Type u → Type v`のようであるべきだが、モナドより前に追加の引数を取ってもよい。
 2. {anchorTerm general}`Monad m`のインスタンスに依拠する、{anchorTerm general}`T m`の{anchorName general}`Monad`インスタンス。これにより変換後のモナドをモナドとして使える。
 3. 任意のモナド{anchorName general}`m`について、型{anchorTerm general}`m α`の動作を型{anchorTerm general}`T m α`の動作に変換する{anchorName general}`MonadLift`インスタンス。これにより、その下にあるモナドの動作を変換後のモナドで使える。

さらに、変換子の{anchorName general}`Monad`インスタンスは、少なくともその下にある{anchorName general}`Monad`インスタンスが守るなら、{anchorName general}`Monad`の契約を守るべきである。
加えて、{anchorTerm general}`monadLift (pure x : m α)`は変換後のモナドにおける{anchorTerm general}`pure x`と等価であるべきであり、{anchorName general}`monadLift`は{anchorName MonadStateT}`bind`に分配すべきである。つまり{anchorTerm general}`monadLift (x >>= f : m α)`は{anchorTerm general}`(monadLift x : m α) >>= fun y => monadLift (f y)`と同じであるべきである。

多くのモナド変換子は、さらに{anchorName m}`MonadReader`の流儀で、そのモナドで実際に使える副作用を記述する型クラスを定義する。
これにより柔軟さが増す。インターフェースだけに依拠し、その下のモナドが特定の変換子で実装されていることを要求しないプログラムを書けるようになる。
型クラスはプログラムが要求を表す手段であり、モナド変換子はその要求を満たす便利な手段である。


# {lit}`OptionT`による失敗
%%%
tag := "OptionT"
%%%

{anchorName OptionExcept}`Option`モナドで表される失敗と、{anchorName M1eval}`Except`モナドで表される例外には、それぞれ対応する変換子がある。
{anchorName OptionTdef}`Option`の場合、本来なら型{anchorName OptionTdef}`α`の値を持つところで型{anchorTerm OptionTdef}`Option α`の値を持つようにすれば、モナドに失敗を加えられる。
たとえば{anchorTerm m}`IO (Option α)`は、いつも型{anchorName m}`α`の値を返すわけではない{anchorName m}`IO`の動作を表す。
これがモナド変換子{anchorName OptionTdef}`OptionT`の定義を示唆する。

```anchor OptionTdef
def OptionT (m : Type u → Type v) (α : Type u) : Type v :=
  m (Option α)
```

{anchorName OptionTdef}`OptionT`が働く例として、利用者に質問するプログラムを考えよう。
{anchorName getSomeInput}`getSomeInput`関数は入力の一行を求め、両端から空白を取り除く。
その結果の切り詰めた入力が空でなければそれを返し、空白でない文字がなければ失敗する。

```anchor getSomeInput
def getSomeInput : OptionT IO String := do
  let input ← (← IO.getStdin).getLine
  let trimmed := input.trimAscii
  if trimmed.isEmpty then
    failure
  else pure trimmed.copy
```
このアプリケーションは利用者を、名前と好きな甲虫の種で記録する。

```anchor UserInfo
structure UserInfo where
  name : String
  favoriteBeetle : String
```
利用者に入力を求めるのは、{anchorName m}`IO`だけを使う関数と比べても冗長ではない。

```anchor getUserInfo
def getUserInfo : OptionT IO UserInfo := do
  IO.println "What is your name?"
  let name ← getSomeInput
  IO.println "What is your favorite species of beetle?"
  let beetle ← getSomeInput
  pure ⟨name, beetle⟩
```
しかし、この関数は{anchorName m}`IO`ではなく{anchorTerm getSomeInput}`OptionT IO`の文脈で動くので、最初の{anchorName getSomeInput}`getSomeInput`の呼び出しが失敗すると{anchorName getUserInfo}`getUserInfo`全体が失敗し、甲虫についての質問には制御が到達しない。
main関数{anchorName interact}`interact`は、純粋に{anchorName m}`IO`の文脈で{anchorName interact}`getUserInfo`を呼び出し、内側の{anchorName m}`Option`でパターンマッチングして、その呼び出しが成功したか失敗したかを調べられる。

```anchor interact
def interact : IO Unit := do
  match ← getUserInfo with
  | none =>
    IO.eprintln "Missing info"
  | some ⟨name, beetle⟩ =>
    IO.println s!"Hello {name}, whose favorite beetle is {beetle}."
```

## Monadインスタンス
%%%
tag := "OptionT-monad-instance"
%%%

モナドのインスタンスを書くと、難点が現れる。
型に基づけば、{anchorName MonadExceptT}`pure`はその下のモナド{anchorName firstMonadOptionT}`m`の{anchorName MonadMissingUni}`pure`を{anchorName firstMonadOptionT}`some`と組み合わせて使うべきである。
{anchorName m}`Option`の{anchorName firstMonadOptionT}`bind`が一つ目の引数で分岐して{anchorName firstMonadOptionT}`none`を伝播させるのと同じように、{anchorName firstMonadOptionT}`OptionT`の{anchorName firstMonadOptionT}`bind`は、一つ目の引数をなすモナドの動作を実行し、その結果で分岐して、{anchorName firstMonadOptionT}`none`を伝播させるべきである。
この下書きに従うと次の定義になるが、Leanはこれを受け付けない。
```anchor firstMonadOptionT
instance [Monad m] : Monad (OptionT m) where
  pure x := pure (some x)
  bind action next := do
    match (← action) with
    | none => pure none
    | some v => next v
```
エラーメッセージは分かりにくい型の食い違いを示す。
```anchorError firstMonadOptionT
Application type mismatch: The argument
  some x
has type
  Option α✝
but is expected to have type
  α✝
in the application
  pure (some x)
```
ここでの問題は、Leanが周囲の{anchorName firstMonadOptionT}`pure`の使用に対して間違った{anchorName firstMonadOptionT}`Monad`インスタンスを選んでいることである。
{anchorName firstMonadOptionT}`bind`の定義でも同様のエラーが起きる。
一つの解決策は、型注釈を使ってLeanを正しい{anchorName MonadOptionTAnnots}`Monad`インスタンスへ導くことである。

```anchor MonadOptionTAnnots
instance [Monad m] : Monad (OptionT m) where
  pure x := (pure (some x) : m (Option _))
  bind action next := (do
    match (← action) with
    | none => pure none
    | some v => next v : m (Option _))
```
この解決策は動くが、優雅ではなく、コードが少し煩わしくなる。

別の解決策は、型シグネチャがLeanを正しいインスタンスへ導く関数を定義することである。
実際、{anchorName OptionTStructure}`OptionT`は構造体として定義できた。

```anchor OptionTStructure
structure OptionT (m : Type u → Type v) (α : Type u) : Type v where
  run : m (Option α)
```
そうすれば問題は解決する。コンストラクタ{anchorName OptionTStructuredefs}`OptionT.mk`とフィールドを取り出す{anchorName OptionTStructuredefs}`OptionT.run`が、型クラスの推論を正しいインスタンスへ導くからである。
そうすることの欠点は、得られるコードがより複雑になり、こうした構造体が証明を読みにくくしうることである。
両方の利点は、コンストラクタ{anchorName OptionTStructuredefs}`OptionT.mk`とフィールド{anchorName OptionTStructuredefs}`OptionT.run`と同じ役割を果たしつつ、直接の定義で働く関数を定義すれば得られる。

```anchor FakeStructOptionT
def OptionT.mk (x : m (Option α)) : OptionT m α := x

def OptionT.run (x : OptionT m α) : m (Option α) := x
```
どちらの関数も入力をそのまま返すが、{anchorName FakeStructOptionT}`OptionT`のインターフェースを示すつもりのコードと、その下のモナド{anchorName FakeStructOptionT}`m`のインターフェースを示すつもりのコードの境界を示す。
これらの補助関数を使うと、{anchorName MonadOptionTFakeStruct}`Monad`インスタンスが読みやすくなる。

```anchor MonadOptionTFakeStruct
instance [Monad m] : Monad (OptionT m) where
  pure x := OptionT.mk (pure (some x))
  bind action next := OptionT.mk do
    match ← action with
    | none => pure none
    | some v => next v
```
ここで{anchorName FakeStructOptionT}`OptionT.mk`を使うのは、その引数が{anchorName MonadOptionTFakeStruct}`m`のインターフェースを使うコードとして扱われるべきことを示しており、これによりLeanが正しい{anchorName MonadOptionTFakeStruct}`Monad`インスタンスを選べる。

モナドのインスタンスを定義したら、モナドの契約が満たされているかを確かめるとよい。
まず、{anchorTerm OptionTFirstLaw}`bind (pure v) f`が{anchorTerm OptionTFirstLaw}`f v`と同じであることを示す。
その段階は次のとおりである。

```anchorEqSteps OptionTFirstLaw
bind (pure v) f
={ /-- `bind` と `pure` の定義を展開する -/
   by simp [bind, pure, OptionT.mk]
}=
OptionT.mk do
  match ← pure (some v) with
  | none => pure none
  | some x => f x
={
/-- 入れ子にした動作の構文を脱糖する -/
}=
OptionT.mk do
  let y ← pure (some v)
  match y with
  | none => pure none
  | some x => f x
={
/-- `do` 記法を脱糖する -/
by simp only [bind_pure, pure_bind]
}=
OptionT.mk
  (pure (some v) >>= fun y =>
    match y with
    | none => pure none
    | some x => f x)
={
  /-- `m` の最初のモナド規則を使う -/
  by simp [LawfulMonad.pure_bind (m := m)]
}=
OptionT.mk
  (match some v with
   | none => pure none
   | some x => f x)
={
/-- `match` を簡約する -/
}=
OptionT.mk (f v)
={
/-- `OptionT.mk` の定義 -/
}=
f v
```

二つ目の規則は、{anchorTerm OptionTSecondLaw}`bind w pure`が{anchorName OptionTSecondLaw}`w`と同じであることを述べている。
これを示すには、{anchorName OptionTSecondLaw}`bind`と{anchorName OptionTSecondLaw}`pure`の定義を展開すると次のようになる。
```anchorTerm OptionTSecondLaw
OptionT.mk do
    match ← w with
    | none => pure none
    | some v => pure (some v)
```
このパターンマッチングでは、どちらの場合の結果も、マッチしているパターンに{anchorName OptionTSecondLaw}`pure`を付けただけのものである。
言い換えれば、これは{anchorTerm OptionTSecondLaw}`w >>= fun y => pure y`と等価であり、{anchorName OptionTFirstLaw}`m`の二つ目のモナド規則の一例である。

最後の規則は、{anchorTerm OptionTThirdLaw}`bind (bind v f) g`が{anchorTerm OptionTThirdLaw}`bind v (fun x => bind (f x) g)`と同じであることを述べている。
これも同じように、{anchorName OptionTThirdLaw}`bind`と{anchorName OptionTSecondLaw}`pure`の定義を展開し、その下のモナド{anchorName OptionTFirstLaw}`m`に委ねれば確かめられる。

## {lit}`Alternative`インスタンス
%%%
tag := "OptionT-Alternative-instance"
%%%

{anchorName OptionTdef}`OptionT`を使う便利な方法の一つは、{anchorName AlternativeOptionT}`Alternative`型クラスを通すことである。
成功の返しは{anchorName AlternativeOptionT}`pure`ですでに示されており、{anchorName AlternativeOptionT}`Alternative`の{anchorName AlternativeOptionT}`failure`と{anchorName AlternativeOptionT}`orElse`メソッドがあれば、複数の部分プログラムのうち最初に成功した結果を返すプログラムを書ける。

```anchor AlternativeOptionT
instance [Monad m] : Alternative (OptionT m) where
  failure := OptionT.mk (pure none)
  orElse x y := OptionT.mk do
    match ← x with
    | some result => pure (some result)
    | none => y ()
```


## 持ち上げ
%%%
tag := "OptionT-lifting"
%%%

{anchorName LiftOptionT}`m`の動作を{anchorTerm LiftOptionT}`OptionT m`へ持ち上げるには、計算の結果を{anchorName LiftOptionT}`some`で包むだけでよい。

```anchor LiftOptionT
instance [Monad m] : MonadLift m (OptionT m) where
  monadLift action := OptionT.mk do
    pure (some (← action))
```


# 例外
%%%
tag := "exceptions"
%%%

{anchorName ExceptT}`Except`のモナド変換子版は、{anchorName m}`Option`のモナド変換子版とよく似ている。
型{anchorTerm ExceptT}`m`{lit}` `{anchorTerm ExceptT}`α`のモナドの動作に型{anchorName ExceptT}`ε`の例外を加えるには、{anchorName MonadExcept}`α`に例外を加えて型{anchorTerm ExceptT}`m (Except ε α)`にすればよい。

```anchor ExceptT
def ExceptT (ε : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
  m (Except ε α)
```
{anchorName OptionTdef}`OptionT`は、型検査器を正しい{anchorName MonadOptionTFakeStruct}`Monad`インスタンスへ導くために{anchorName FakeStructOptionT}`OptionT.mk`と{anchorName FakeStructOptionT}`OptionT.run`の関数を用意している。
この工夫は{anchorName ExceptTFakeStruct}`ExceptT`にも役に立つ。

```anchor ExceptTFakeStruct
  def ExceptT.mk {ε α : Type u} (x : m (Except ε α)) : ExceptT ε m α := x

  def ExceptT.run {ε α : Type u} (x : ExceptT ε m α) : m (Except ε α) := x
```
{anchorName MonadExceptT}`ExceptT`の{anchorName MonadExceptT}`Monad`インスタンスも{anchorName MonadOptionTFakeStruct}`OptionT`のインスタンスとよく似ている。
唯一の違いは、{anchorName MonadOptionTFakeStruct}`none`ではなく具体的なエラーの値を伝播させることである。

```anchor MonadExceptT
instance {ε : Type u} {m : Type u → Type v} [Monad m] :
    Monad (ExceptT ε m) where
  pure x := ExceptT.mk (pure (Except.ok x))
  bind result next := ExceptT.mk do
    match ← result with
    | .error e => pure (.error e)
    | .ok x => next x
```

{anchorName ExceptTFakeStruct}`ExceptT.mk`と{anchorName ExceptTFakeStruct}`ExceptT.run`の型シグネチャには細かな点がある。{anchorName ExceptTFakeStruct}`α`と{anchorName ExceptTFakeStruct}`ε`の宇宙の段階を明示的に注記しているのである。
明示的に注記しなければ、Leanはそれらが別々の多相的な宇宙の変数を持つ、より一般的な型シグネチャを生成する。
しかし、{anchorName ExceptTFakeStruct}`ExceptT`の定義はそれらが同じ宇宙にあることを期待する。どちらも{anchorName ExceptTFakeStruct}`m`の引数として与えられうるためである。
これにより、{anchorName MonadStateT}`Monad`インスタンスで宇宙の段階の解決器が働く解を見つけられない問題が起きうる。

```anchor ExceptTNoUnis
def ExceptT.mk (x : m (Except ε α)) : ExceptT ε m α := x
```
```anchor MonadMissingUni
instance {ε : Type u} {m : Type u → Type v} [Monad m] :
    Monad (ExceptT ε m) where
  pure x := ExceptT.mk (pure (Except.ok x))
  bind result next := ExceptT.mk do
    match (← result) with
    | .error e => pure (.error e)
    | .ok x => next x
```
```anchorError MonadMissingUni
stuck at solving universe constraint
  max ?u.10439 ?u.10440 =?= u
while trying to unify
  ExceptT ε m β✝ : Type v
with
  ExceptT.{max ?u.10440 ?u.10439, v} ε m β✝ : Type v
```
この種のエラーメッセージは通常、制約の足りない宇宙の変数によって引き起こされる。
原因を突き止めるのは難しいこともあるが、まず、ある定義では使い回されている宇宙の変数が別の定義では使い回されていない箇所を探すとよい。

{anchorName m}`Option`と違い、{anchorName m}`Except`データ型は通常、データ構造として使わない。
常に{anchorName MonadExceptT}`Monad`インスタンスとともに制御構造として使う。
つまり、{anchorTerm ExceptTLiftExcept}`Except ε`の動作を{anchorTerm ExceptTLiftExcept}`ExceptT ε m`へ持ち上げるのはもっともであり、その下のモナド{anchorName ExceptTLiftExcept}`m`の動作についても同様である。
{anchorName ExceptTLiftExcept}`Except`の動作を{anchorName ExceptTLiftExcept}`ExceptT`の動作へ持ち上げるには、{anchorName ExceptTLiftExcept}`m`の{anchorName ExceptTLiftExcept}`pure`で包む。例外の副作用しか持たない動作は{anchorName ExceptTLiftExcept}`m`の副作用を持ちえないためである。

```anchor ExceptTLiftExcept
instance [Monad m] : MonadLift (Except ε) (ExceptT ε m) where
  monadLift action := ExceptT.mk (pure action)
```
{anchorName ExceptTLiftExcept}`m`の動作には例外がないので、その値は{anchorName MonadExceptT}`Except.ok`で包むべきである。
これは、{anchorName various}`Functor`が{anchorName various}`Monad`の上位クラスであることを使えば実現できる。モナドの計算の結果に関数を適用するのは{anchorName various}`Functor.map`で行える。

```anchor ExceptTLiftM
instance [Monad m] : MonadLift m (ExceptT ε m) where
  monadLift action := ExceptT.mk (.ok <$> action)
```

## 例外のための型クラス
%%%
tag := "exceptions-type-classes"
%%%

例外処理は根本的に二つの操作から成る。例外を投げる能力と、それから復帰する能力である。
これまでは、それぞれ{anchorName m}`Except`のコンストラクタとパターンマッチングで行ってきた。
しかし、これでは例外を使うプログラムが、例外処理という副作用の特定の符号化に縛られる。
これらの操作をとらえるのに型クラスを使えば、例外を使うプログラムを、投げることと捕まえることを支える*どの*モナドでも使える。

例外を投げる操作は例外を引数に取り、モナドの動作が要求されるどの文脈でも許されるべきである。
仕様の「どの文脈でも」という部分は、型{anchorTerm MonadExcept}`m α`と書くことで表せる。任意の型の値を生み出す方法はないので、{anchorName MonadExcept}`throw`操作は、制御をプログラムのその部分から去らせる何かをしているはずである。
例外を捕まえる操作は、任意のモナドの動作と処理役を受け取り、その処理役は例外からその動作の型へどう戻るかを示すべきである。

```anchor MonadExcept
class MonadExcept (ε : outParam (Type u)) (m : Type v → Type w) where
  throw : ε → m α
  tryCatch : m α → (ε → m α) → m α
```

{anchorName MonadExcept}`MonadExcept`の宇宙の段階は{anchorName ExceptT}`ExceptT`のものと異なる。
{anchorName ExceptT}`ExceptT`では{anchorName ExceptT}`ε`と{anchorName ExceptT}`α`が同じ段階にあるが、{anchorName MonadExcept}`MonadExcept`はそのような制限を課さない。
{anchorName MonadExcept}`MonadExcept`は例外の値を{anchorName MonadExcept}`m`の中に入れることがないためである。
最も一般的な宇宙のシグネチャは、この定義で{anchorName MonadExcept}`ε`と{anchorName MonadExcept}`α`がまったく独立であるという事実を認めている。
より一般的であるということは、その型クラスをより多くの種類の型で具体化できるということである。

{anchorName MonadExcept}`MonadExcept`を使うプログラムの例として、簡単な除算のサービスがある。
このプログラムは二つの部分に分かれる。エラーを扱う、文字列に基づく利用者向けの画面を与えるフロントエンドと、実際に除算を行うバックエンドである。
フロントエンドもバックエンドも例外を投げられ、前者は不正な入力に対して、後者はゼロによる除算に対して投げる。
例外は帰納型である。

```anchor ErrEx
inductive Err where
  | divByZero
  | notANumber : String → Err
```
バックエンドはゼロかどうかを調べ、可能なら除算する。

```anchor divBackend
def divBackend [Monad m] [MonadExcept Err m] (n k : Int) : m Int :=
  if k == 0 then
    throw .divByZero
  else pure (n / k)
```
フロントエンドの補助関数{anchorName asNumber}`asNumber`は、渡された文字列が数でなければ例外を投げる。
フロントエンド全体は入力を{anchorName asNumber}`Int`に変換してバックエンドを呼び、例外を扱って分かりやすい文字列のエラーを返す。

```anchor asNumber
def asNumber [Monad m] [MonadExcept Err m] (s : String) : m Int :=
  match s.toInt? with
  | none => throw (.notANumber s)
  | some i => pure i
```

```anchor divFrontend
def divFrontend [Monad m] [MonadExcept Err m] (n k : String) : m String :=
  tryCatch (do pure (toString (← divBackend (← asNumber n) (← asNumber k))))
    fun
      | .divByZero => pure "Division by zero!"
      | .notANumber s => pure s!"Not a number: \"{s}\""
```
例外を投げることと捕まえることはよくあるので、Leanには{anchorName divFrontendSugary}`MonadExcept`を使うための特別な構文がある。
{lit}`+`が{anchorName various}`HAdd.hAdd`の略であるのと同じように、{kw}`try`と{kw}`catch`を{anchorName MonadExcept}`tryCatch`メソッドの略として使える。

```anchor divFrontendSugary
def divFrontend [Monad m] [MonadExcept Err m] (n k : String) : m String :=
  try
    pure (toString (← divBackend (← asNumber n) (← asNumber k)))
  catch
    | .divByZero => pure "Division by zero!"
    | .notANumber s => pure s!"Not a number: \"{s}\""
```

{anchorName m}`Except`と{anchorName ExceptT}`ExceptT`に加えて、一見すると例外には見えない他の型にも役に立つ{anchorName MonadExcept}`MonadExcept`インスタンスがある。
たとえば{anchorName m}`Option`による失敗は、まったくデータを含まない例外を投げることと見なせるので、{anchorName m}`Option`で{kw}`try`{lit}` ...`{kw}`catch`{lit}` ...`構文を使えるようにする{anchorTerm OptionExcept}`MonadExcept Unit Option`のインスタンスがある。

# 状態
%%%
tag := "state-monad"
%%%

可変状態のまねごとは、モナドの動作が開始時の状態を引数に取り、最終状態をその結果とともに返すようにすれば、モナドに加えられる。
状態モナドのbind演算子は、ある動作の最終状態を次の動作の引数として与え、プログラムを通して状態を受け渡す。
このパターンもモナド変換子として表せる。

```anchor DefStateT
def StateT (σ : Type u)
    (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (α × σ)
```


ここでもまた、モナドのインスタンスは{anchorName State (module := Examples.Monads)}`State`のものとよく似ている。
唯一の違いは、入力と出力の状態が、純粋なコードではなくその下のモナドで受け渡され、返されることである。

```anchor MonadStateT
instance [Monad m] : Monad (StateT σ m) where
  pure x := fun s => pure (x, s)
  bind result next := fun s => do
    let (v, s') ← result s
    next v s'
```

対応する型クラスには{anchorName MonadState}`get`と{anchorName MonadState}`set`メソッドがある。
{anchorName MonadState}`get`と{anchorName MonadState}`set`の欠点の一つは、更新するときに間違った状態を{anchorName MonadState}`set`しやすくなりすぎることである。
状態を取り出し、更新し、更新した状態を保存するという書き方が、ある種のプログラムでは自然だからである。
たとえば、次のプログラムは文字列にある、分音符号のない英語の母音と子音の数を数える。

```anchor countLetters
structure LetterCounts where
  vowels : Nat
  consonants : Nat
deriving Repr

inductive Err where
  | notALetter : Char → Err
deriving Repr

def vowels :=
  let lowerVowels := "aeiuoy"
  lowerVowels ++ lowerVowels.map (·.toUpper)

def consonants :=
  let lowerConsonants := "bcdfghjklmnpqrstvwxz"
  lowerConsonants ++ lowerConsonants.map (·.toUpper )

def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      let st ← get
      let st' ←
        if c.isAlpha then
          if vowels.contains c then
            pure {st with vowels := st.vowels + 1}
          else if consonants.contains c then
            pure {st with consonants := st.consonants + 1}
          else -- modified or non-English letter
            pure st
        else throw (.notALetter c)
      set st'
      loop cs
  loop str.toList
```
{anchorTerm countLetters}`set st'`の代わりに{lit}`set st`と書いてしまうのはとてもたやすい。
大きなプログラムでは、この種の間違いが原因の分かりにくい不具合につながりうる。

{anchorName countLetters}`get`の呼び出しに入れ子にした動作を使えばこの問題は解決するが、この種の問題すべてを解決できるわけではない。
たとえば、ある関数が構造体のフィールドを、他の二つのフィールドの値に基づいて更新することがある。
その場合、{anchorName countLetters}`get`への入れ子にした動作の呼び出しが二つ必要になる。
Leanのコンパイラには、ある値への参照が一つだけのときにしか効かない最適化があるので、状態への参照を複製すると、著しく遅いコードになることがある。
性能の問題と不具合の可能性のどちらも、関数を使って状態を変換する{anchorName countLettersModify}`modify`を使えば避けられる。

```anchor countLettersModify
def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        else -- modified or non-English letter
          pure ()
      else throw (.notALetter c)
      loop cs
  loop str.toList
```
この型クラスには{anchorName modify}`modify`に似た{anchorName modify}`modifyGet`という関数があり、一つの段階で戻り値を計算すると同時に古い状態を変換できる。
この関数は、一つ目の要素が戻り値、二つ目の要素が新しい状態である組を返す。{anchorName modify}`modify`は、{anchorName modify}`modifyGet`で使う組に{anchorName modify}`Unit`のコンストラクタを付けるだけである。

```anchor modify
def modify [MonadState σ m] (f : σ → σ) : m Unit :=
  modifyGet fun s => ((), f s)
```

{anchorName MonadState}`MonadState`の定義は次のとおりである。

```anchor MonadState
class MonadState (σ : outParam (Type u)) (m : Type u → Type v) :
    Type (max (u+1) v) where
  get : m σ
  set : σ → m PUnit
  modifyGet : (σ → α × σ) → m α
```
{anchorName MonadState}`PUnit`は{anchorName modify}`Unit`型の一種で、{anchorTerm MonadState}`Type`ではなく{anchorTerm MonadState}`Type u`に置けるように宇宙多相になっている。
{anchorName MonadState}`get`と{anchorName MonadState}`set`を使った{anchorName MonadState}`modifyGet`の既定の実装を用意することは可能だが、それでは{anchorName MonadState}`modifyGet`を役に立たせている最適化が使えず、このメソッドが無意味になる。

# {lit}`Of`クラスと{lit}`The`関数
%%%
tag := "of-and-the"
%%%

これまで、{anchorName MonadExcept}`MonadExcept`の例外の型や{anchorName MonadState}`MonadState`の状態の型のように追加の情報を取るモナドの型クラスは、その追加の情報の型を出力パラメータとして持っていた。
簡単なプログラムでは、これは一般に便利である。{anchorName MonadStateT}`StateT`、{anchorName m}`ReaderT`、{anchorName ExceptT}`ExceptT`をそれぞれ一つずつ組み合わせたモナドは、状態の型、環境の型、例外の型をそれぞれ一つしか持たないからである。
しかし、モナドが複雑になると、複数の状態や複数のエラーの型を関わらせることがある。
この場合、出力パラメータを使うと、同じ{kw}`do`ブロックで両方の状態を対象にできない。

こうした場合のために、追加の情報が出力パラメータでない型クラスが別にある。
これらの版の型クラスは名前に{lit}`Of`を含む。
たとえば{anchorName getTheType}`MonadStateOf`は{anchorName MonadState}`MonadState`に似ているが、{anchorName MonadState}`outParam`修飾子がない。

これらのクラスは{anchorName MonadState}`outParam`の代わりに、それぞれの状態、環境、例外の型に{anchorName various}`semiOutParam`を使う。
{anchorName MonadState}`outParam`と同じく、{anchorName various}`semiOutParam`もLeanがインスタンスの探索を始める前に分かっている必要はない。
しかし重要な違いがある。{anchorName MonadState}`outParam`はインスタンスの探索中は無視され、その結果、真に出力である。
{anchorName MonadState}`outParam`が探索の前に分かっていれば、Leanは探索の結果が分かっていたものと同じかを調べるだけである。
一方、探索の開始前に分かっている{anchorName various}`semiOutParam`は、入力パラメータと同じように候補を絞るのに使える。

状態モナドの状態の型が{anchorName MonadState}`outParam`なら、各モナドは状態の型を高々一つしか持てない。
これは便利である。型推論がよくなり、より多くの状況で状態の型を推論できるからである。
また不便でもある。{anchorName countLetters}`StateT`を複数組み合わせて作ったモナドは、役に立つ{anchorName modify}`MonadState`インスタンスを提供できないからである。
しかし{anchorName modifyTheType}`MonadStateOf`を使うと、どのインスタンスを使うかを選ぶのに使えるときにはLeanが状態の型を考慮するので、一つのモナドが複数の型の状態を提供してもよい。
その欠点は、状態の型が十分に明示されていないときに、得られるインスタンスが意図したものと違うことがあり、紛らわしいエラーメッセージにつながることである。

同様に、追加の情報の型を暗黙の引数ではなく*明示的な*引数として受け取る版の型クラスのメソッドもある。
{anchorName modifyTheType}`MonadStateOf`には、型が次のものである{anchorTerm getTheType}`getThe`がある。
```anchorTerm getTheType
(σ : Type u) → {m : Type u → Type v} → [MonadStateOf σ m] → m σ
```
また、型が次のものである{anchorTerm modifyTheType}`modifyThe`がある。
```anchorTerm modifyTheType
(σ : Type u) → {m : Type u → Type v} → [MonadStateOf σ m] → (σ → σ) → m PUnit
```
{lit}`setThe`はない。新しい状態の型だけで、どの周囲の状態モナド変換子を使うかを決められるためである。

Leanの標準ライブラリでは、{lit}`Of`の付かない版のクラスのインスタンスが、{lit}`Of`の付く版のインスタンスを使って定義されている。
言い換えれば、{lit}`Of`の付く版を実装すると両方の実装が得られる。
一般には、{lit}`Of`の付く版を実装し、まず{lit}`Of`の付かない版のクラスを使ってプログラムを書き始め、出力パラメータが不便になったら{lit}`Of`の付く版へ移るのがよい。

# 変換子と{lit}`Id`
%%%
tag := "transformers-and-Id"
%%%

恒等モナド{anchorName various}`Id`は、副作用をまったく持たないモナドであり、何らかの理由でモナドを期待するが実際には不要な文脈で使う。
{anchorName various}`Id`のもう一つの用途は、モナド変換子の積み重ねの底として働くことである。
たとえば{anchorTerm StateTDoubleB}`StateT σ Id`は{anchorTerm set (module:=Examples.Monads)}`State σ`とまったく同じように働く。


# 練習問題
%%%
tag := "monad-transformer-exercises"
%%%

## モナドの契約
%%%
tag := none
%%%

紙と鉛筆を使って、この節の各モナド変換子についてモナド変換子の契約の規則が満たされていることを確かめよ。

## ログの変換子
%%%
tag := none
%%%

{anchorName WithLog (module:=Examples.Monads)}`WithLog`のモナド変換子版を定義せよ。
また、対応する型クラス{lit}`MonadWithLog`を定義し、ログと例外を組み合わせたプログラムを書け。

## ファイルの数え上げ
%%%
tag := none
%%%

{lit}`doug`のモナドを{anchorName MonadStateT}`StateT`で変更し、見たディレクトリとファイルの数を数えるようにせよ。
実行の最後に、次のような報告を表示するものとする。
```
  Viewed 38 files in 5 directories.
```
