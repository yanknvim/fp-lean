module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.FunctorApplicativeMonad"

#doc (Manual) "The Applicative Contract" =>
%%%
tag := "applicative-laws"
%%%

{anchorName ApplicativeLaws}`Functor`、{anchorName ApplicativeLaws}`Monad`、そして{anchorName SizedCreature}`BEq`と{anchorName MonstrousAssistantMore}`Hashable`を実装する型と同じく、{anchorName ApplicativeLaws}`Applicative`にも、すべてのインスタンスが守るべき規則がある。

アプリカティブファンクタが従うべき規則は四つある。
1. 恒等性を尊重する。つまり{anchorTerm ApplicativeLaws}`pure id <*> v = v`。
2. 関数の合成を尊重する。つまり{anchorTerm ApplicativeLaws}`pure (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)`。
3. 純粋な操作をつなげても何も変わらない。つまり{anchorTerm ApplicativeLaws}`pure f <*> pure x`{lit}` = `{anchorTerm ApplicativeLaws}`pure (f x)`。
4. 純粋な操作の順序は問題にならない。つまり{anchorTerm ApplicativeLaws}`u <*> pure x = pure (fun f => f x) <*> u`。

{anchorTerm ApplicativeOption}`Applicative Option`インスタンスについてこれらを確かめるには、まず{anchorName ApplicativeLaws}`pure`を{anchorName ApplicativeOption}`some`に展開する。

一つ目の規則は{anchorTerm ApplicativeOptionLaws1}`some id <*> v = v`を述べている。
{anchorName ApplicativeOption}`Option`の{anchorName fakeSeq}`seq`の定義によれば、これは{anchorTerm ApplicativeOptionLaws1}`id <$> v = v`と同じであり、すでに確かめた{anchorName ApplicativeLaws}`Functor`の規則の一つである。

二つ目の規則は{anchorTerm ApplicativeOptionLaws2}`some (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)`を述べている。
{anchorName ApplicativeOptionLaws2}`u`、{anchorName ApplicativeOptionLaws2}`v`、{anchorName ApplicativeOptionLaws2}`w`のどれかが{anchorName ApplicativeOption}`none`なら、両辺とも{anchorName ApplicativeOption}`none`なので性質は成り立つ。
{anchorName ApplicativeOptionLaws2}`u`が{anchorTerm OptionHomomorphism1}`some f`、{anchorName ApplicativeOptionLaws2}`v`が{anchorTerm OptionHomomorphism1}`some g`、{anchorName ApplicativeOptionLaws2}`w`が{anchorTerm OptionHomomorphism1}`some x`とすると、これは{anchorTerm OptionHomomorphism}`some (· ∘ ·) <*> some f <*> some g <*> some x = some f <*> (some g <*> some x)`と言うのと同じである。
両辺を評価すると同じ結果になる。
```anchorEvalSteps OptionHomomorphism1
some (· ∘ ·) <*> some f <*> some g <*> some x
===>
some (f ∘ ·) <*> some g <*> some x
===>
some (f ∘ g) <*> some x
===>
some ((f ∘ g) x)
===>
some (f (g x))
```
```anchorEvalSteps OptionHomomorphism2
some f <*> (some g <*> some x)
===>
some f <*> (some (g x))
===>
some (f (g x))
```

三つ目の規則は{anchorName fakeSeq}`seq`の定義から直接従う。
```anchorEvalSteps OptionPureSeq
some f <*> some x
===>
f <$> some x
===>
some (f x)
```

四つ目の場合は、{anchorName ApplicativeLaws}`u`を{anchorTerm OptionPureSeq}`some f`と仮定する。{anchorName AlternativeOption}`none`なら等式の両辺とも{anchorName AlternativeOption}`none`になるためである。
{anchorTerm OptionPureSeq}`some f <*> some x`は直接{anchorTerm OptionPureSeq}`some (f x)`に評価され、{anchorTerm OptionPureSeq2}`some (fun g => g x) <*> some f`も同様である。


# すべてのアプリカティブはファンクタである
%%%
tag := "applicatives-are-functors"
%%%

{anchorName ApplicativeMap}`Applicative`の二つの演算子があれば{anchorName ApplicativeMap}`map`を定義できる。

```anchor ApplicativeMap
def map [Applicative f] (g : α → β) (x : f α) : f β :=
  pure g <*> x
```

ただし、これを{anchorName ApplicativeLaws}`Functor`の実装に使えるのは、{anchorName ApplicativeLaws}`Applicative`の契約が{anchorName ApplicativeLaws}`Functor`の契約を保証する場合だけである。
{anchorName ApplicativeLaws}`Functor`の一つ目の規則は{anchorTerm AppToFunTerms}`id <$> x = x`であり、これは{anchorName ApplicativeLaws}`Applicative`の一つ目の規則から直接従う。
{anchorName ApplicativeLaws}`Functor`の二つ目の規則は{anchorTerm AppToFunTerms}`map (f ∘ g) x = map f (map g x)`である。
ここで{anchorName AppToFunTerms}`map`の定義を展開すると{anchorTerm AppToFunTerms}`pure (f ∘ g) <*> x = pure f <*> (pure g <*> x)`になる。
純粋な操作をつなげても何も変わらないという規則を使うと、左辺は{anchorTerm AppToFunTerms}`pure (· ∘ ·) <*> pure f <*> pure g <*> x`に書き換えられる。
これは、アプリカティブファンクタが関数の合成を尊重するという規則の一例である。

これにより、{anchorName ApplicativeLaws}`Functor`を継承し、{anchorName ApplicativeExtendsFunctorOne}`pure`と{anchorName ApplicativeExtendsFunctorOne}`seq`を使った{anchorTerm ApplicativeExtendsFunctorOne}`map`の既定の定義を持つ{anchorName ApplicativeMap}`Applicative`の定義が正当化される。

```anchor ApplicativeExtendsFunctorOne
class Applicative (f : Type → Type) extends Functor f where
  pure : α → f α
  seq : f (α → β) → (Unit → f α) → f β
  map g x := seq (pure g) (fun () => x)
```

# すべてのモナドはアプリカティブファンクタである
%%%
tag :="monads-are-applicative"
%%%

{anchorName MonadExtends}`Monad`のインスタンスには、すでに{anchorName MonadSeq}`pure`の実装が要る。
{anchorName MonadExtends}`bind`と合わせれば、{anchorName MonadSeq}`seq`を定義するのに十分である。

```anchor MonadSeq
def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  let g ← f
  let y ← x ()
  pure (g y)
```
ここでもまた、{anchorName MonadSeq}`Monad`の契約が{anchorName MonadExtends}`Applicative`の契約を含むことを確かめれば、{anchorName MonadSeq}`Monad`が{anchorName MonadExtends}`Applicative`を継承するときの{anchorTerm MonadExtends}`seq`の既定の定義としてこれを使える。

この節の残りは、{anchorName MonadExtends}`bind`に基づくこの{anchorTerm MonadExtends}`seq`の実装が実際に{anchorName MonadExtends}`Applicative`の契約を満たすという議論である。
関数型プログラミングの美点の一つは、この種の議論を、{ref "evaluating"}[式の評価についての最初の節]のような評価の規則を使って、紙と鉛筆で組み立てられることである。
これらの議論を読みながら操作の意味を考えると、理解の助けになることもある。

{kw}`do`記法を{lit}`>>=`の明示的な使用に置き換えると、{anchorName MonadSeqDesugar}`Monad`の規則を適用しやすくなる。

```anchor MonadSeqDesugar
def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β :=
  f >>= fun g =>
  x () >>= fun y =>
  pure (g y)
```


この定義が恒等性を尊重することを確かめるには、{anchorTerm mSeqRespIdInit}`seq (pure id) (fun () => v) = v`を確かめる。
左辺は{anchorTerm mSeqRespIdInit}`pure id >>= fun g => (fun () => v) () >>= fun y => pure (g y)`と等しい。
真ん中にあるunitの関数はすぐに取り除け、{anchorTerm mSeqRespIdInit}`pure id >>= fun g => v >>= fun y => pure (g y)`になる。
{anchorName mSeqRespIdInit}`pure`が{anchorTerm mSeqRespIdInit}`>>=`の左単位元であることを使うと、これは{anchorTerm mSeqRespIdInit}`v >>= fun y => pure (id y)`と同じであり、つまり{anchorTerm mSeqRespIdInit}`v >>= fun y => pure y`である。
{anchorTerm mSeqRespIdInit}`fun x => f x`は{anchorName mSeqRespIdInit}`f`と同じなので、これは{anchorTerm mSeqRespIdInit}`v >>= pure`と同じであり、{anchorName mSeqRespIdInit}`pure`が{anchorTerm mSeqRespIdInit}`>>=`の右単位元であることを使うと{anchorName mSeqRespIdInit}`v`が得られる。

この種の非形式的な推論は、少し書き方を変えると読みやすくなる。
次の図では、「{lit}`EXPR1 ={ REASON }= EXPR2`」を「{lit}`REASON`という理由で{lit}`EXPR1`は{lit}`EXPR2`と同じ」と読む。

```anchorEqSteps mSeqRespId
pure id >>= fun g => v >>= fun y => pure (g y)
={
/-- `pure` は `>>=` の左単位元 -/
by simp [LawfulMonad.pure_bind]
}=
v >>= fun y => pure (id y)
={
/-- `id` の呼び出しを簡約する -/
}=
v >>= fun y => pure y
={
/-- `fun x => f x` は `f` と同じ -/
by
  have {α β } {f : α → β} : (fun x => f x) = (f) := rfl
  rfl
}=
v >>= pure
={
/-- `pure` は `>>=` の右単位元 -/
by simp
}=
v
```



関数の合成を尊重することを確かめるには、{anchorTerm ApplicativeLaws}`pure (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)`を確かめる。
まず、{lit}`<*>`をこの{anchorName MonadSeqDesugar}`seq`の定義で置き換える。
そのあとは、{anchorName ApplicativeLaws}`Monad`の契約の単位元と結合性の規則を使う（やや長い）一連の段階を踏めば、一方から他方へ到達できる。
```anchorEqSteps mSeqRespComp
seq (seq (seq (pure (· ∘ ·)) (fun _ => u))
      (fun _ => v))
  (fun _ => w)
={
/-- `seq` の定義 -/
}=
((pure (· ∘ ·) >>= fun f =>
   u >>= fun x =>
   pure (f x)) >>= fun g =>
  v >>= fun y =>
  pure (g y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
={
/-- `pure` は `>>=` の左単位元 -/
by simp only [LawfulMonad.pure_bind]
}=
((u >>= fun x =>
   pure (x ∘ ·)) >>= fun g =>
   v >>= fun y =>
  pure (g y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
={
/-- 分かりやすさのため括弧を挿入 -/
}=
((u >>= fun x =>
   pure (x ∘ ·)) >>= (fun g =>
   v >>= fun y =>
  pure (g y))) >>= fun h =>
 w >>= fun z =>
 pure (h z)
={
/-- `>>=` の結合性 -/
by simp only [LawfulMonad.bind_assoc]
}=
(u >>= fun x =>
  pure (x ∘ ·) >>= fun g =>
 v  >>= fun y => pure (g y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
={
/-- `pure` は `>>=` の左単位元 -/
by simp only [LawfulMonad.pure_bind]
}=
(u >>= fun x =>
  v >>= fun y =>
  pure (x ∘ y)) >>= fun h =>
 w >>= fun z =>
 pure (h z)
={
/-- `>>=` の結合性 -/
by simp only [LawfulMonad.bind_assoc]
}=
u >>= fun x =>
v >>= fun y =>
pure (x ∘ y) >>= fun h =>
w >>= fun z =>
pure (h z)
={
/-- `pure` は `>>=` の左単位元 -/
by simp [bind_pure_comp]; rfl
}=
u >>= fun x =>
v >>= fun y =>
w >>= fun z =>
pure ((x ∘ y) z)
={
/-- 関数の合成の定義 -/
}=
u >>= fun x =>
v >>= fun y =>
w >>= fun z =>
pure (x (y z))
={
/--
ここから逆向きに進む。
`pure` は `>>=` の左単位元
-/
by simp
}=
u >>= fun x =>
v >>= fun y =>
w >>= fun z =>
pure (y z) >>= fun q =>
pure (x q)
={
/-- `>>=` の結合性 -/
by simp
}=
u >>= fun x =>
v >>= fun y =>
 (w >>= fun p =>
  pure (y p)) >>= fun q =>
 pure (x q)
={
/-- `>>=` の結合性 -/
by simp
}=
u >>= fun x =>
 (v >>= fun y =>
  w >>= fun q =>
  pure (y q)) >>= fun z =>
 pure (x z)
={
/-- ここには `seq` の定義も含まれる -/
}=
u >>= fun x =>
seq v (fun () => w) >>= fun q =>
pure (x q)
={
/-- ここにも `seq` の定義が含まれる -/
}=
seq u (fun () => seq v (fun () => w))
```


純粋な操作をつなげても何も変わらないことを確かめるには、次のようにする。
```anchorEqSteps mSeqPureNoOp
seq (pure f) (fun () => pure x)
={
/-- `seq` をその定義で置き換える -/
}=
pure f >>= fun g =>
pure x >>= fun y =>
pure (g y)
={
/-- `pure` は `>>=` の左単位元 -/
by simp
}=
pure f >>= fun g =>
pure (g x)
={
/-- `pure` は `>>=` の左単位元 -/
by simp
}=
pure (f x)
```


最後に、純粋な操作の順序が問題にならないことを確かめる。
```anchorEqSteps mSeqPureNoOrder
seq u (fun () => pure x)
={
/-- `seq` の定義 -/
}=
u >>= fun f =>
pure x >>= fun y =>
pure (f y)
={
/-- `pure` は `>>=` の左単位元 -/
by simp
}=
u >>= fun f =>
pure (f x)
={
/-- 規則が当てはまるように、ある式を等価な式で巧みに置き換える -/
}=
u >>= fun f =>
pure ((fun g => g x) f)
={
/-- `pure` は `>>=` の左単位元 -/
by simp [LawfulMonad.pure_bind]
}=
pure (fun g => g x) >>= fun h =>
u >>= fun f =>
pure (h f)
={
/-- `seq` の定義 -/
}=
seq (pure (fun f => f x)) (fun () => u)
```


これにより、{anchorName ApplicativeLaws}`Applicative`を継承し、{anchorTerm MonadExtends}`seq`の既定の定義を持つ{anchorName ApplicativeLaws}`Monad`の定義が正当化される。

```anchor MonadExtends
class Monad (m : Type → Type) extends Applicative m where
  bind : m α → (α → m β) → m β
  seq f x :=
    bind f fun g =>
    bind (x ()) fun y =>
    pure (g y)
```
{anchorName MonadExtends}`Applicative`自身の{anchorTerm ApplicativeExtendsFunctorOne}`map`の既定の定義により、どの{anchorName MonadExtends}`Monad`インスタンスも{anchorName MonadExtends}`Applicative`と{anchorName ApplicativeExtendsFunctorOne}`Functor`のインスタンスも自動で生成する。

# 追加の取り決め
%%%
tag := "additional-stipulations"
%%%

各型クラスに付随する個々の契約を守ることに加えて、{anchorName ApplicativeLaws}`Functor`、{anchorName ApplicativeLaws}`Applicative`、{anchorName ApplicativeLaws}`Monad`を組み合わせた実装は、これらの既定の実装と同じように働くべきである。
言い換えれば、{anchorName ApplicativeLaws}`Applicative`と{anchorName ApplicativeLaws}`Monad`の両方のインスタンスを提供する型は、{anchorName MonadSeq}`Monad`インスタンスが既定の実装として生成する版と違う働きをする{anchorTerm MonadExtends}`seq`の実装を持ってはならない。
これは重要である。多相的な関数は、{lit}`>>=`の使用を等価な{lit}`<*>`の使用に置き換えたり、{lit}`<*>`の使用を等価な{lit}`>>=`の使用に置き換えたりするように書き換えられることがあるためである。
この書き換えで、そのコードを使うプログラムの意味が変わってはならない。

この規則は、{anchorName ValidateAndThen}`Validate.andThen`を{anchorName ApplicativeLaws}`Monad`インスタンスの{anchorName MonadExtends}`bind`の実装に使うべきでない理由を説明する。
それ自体はモナドの契約を満たす。
しかし、これを{anchorTerm MonadExtends}`seq`の実装に使うと、その振る舞いは{anchorTerm MonadExtends}`seq`自体と等価でなくなる。
どこが違うかを見るには、どちらもエラーを返す二つの計算の例を考えよう。
まず、二つのエラーが返るべき場合の例から始める。一つは関数の検査によるもの（これはその関数の前の引数の検査によるものでもよかった）、もう一つは引数の検査によるものである。

```anchor counterexample
def notFun : Validate String (Nat → String) :=
  .errors { head := "First error", tail := [] }

def notArg : Validate String Nat :=
  .errors { head := "Second error", tail := [] }
```

これらを{anchorName Validate}`Validate`の{anchorName ApplicativeValidate}`Applicative`インスタンスの{lit}`<*>`の版で組み合わせると、二つのエラーがどちらも利用者に報告される。
```anchorEvalSteps realSeq
notFun <*> notArg
===>
match notFun with
| .ok g => g <$> notArg
| .errors errs =>
  match notArg with
  | .ok _ => .errors errs
  | .errors errs' => .errors (errs ++ errs')
===>
match notArg with
| .ok _ =>
  .errors { head := "First error", tail := [] }
| .errors errs' =>
  .errors ({ head := "First error", tail := [] } ++ errs')
===>
.errors
  ({ head := "First error", tail := [] } ++
   { head := "Second error", tail := []})
===>
.errors {
  head := "First error",
  tail := ["Second error"]
}
```

{lit}`>>=`で実装した版の{anchorName MonadSeqDesugar}`seq`（ここでは{anchorName fakeSeq}`andThen`に書き換えている）を使うと、最初のエラーだけが得られる。
```anchorEvalSteps fakeSeq
seq notFun (fun () => notArg)
===>
notFun.andThen fun g =>
notArg.andThen fun y =>
pure (g y)
===>
match notFun with
| .errors errs => .errors errs
| .ok val =>
  (fun g =>
    notArg.andThen fun y =>
    pure (g y)) val
===>
.errors { head := "First error", tail := [] }
```
