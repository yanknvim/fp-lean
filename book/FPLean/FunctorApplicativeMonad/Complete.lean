module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.FunctorApplicativeMonad.ActualDefs"

#doc (Manual) "The Complete Definitions" =>
%%%
tag := "complete-definitions"
%%%

関係する言語機能をすべて紹介したので、この節では、Leanの標準ライブラリにあるままの、{anchorName HonestFunctor}`Functor`、{anchorName Applicative}`Applicative`、{anchorName Monad}`Monad`の完全で正直な定義を述べる。
理解のために、細部は一切省かない。

# ファンクタ
%%%
tag := "complete-functor-definition"
%%%


The complete definition of the {anchorName Applicative}`Functor`クラスの完全な定義は、宇宙多相と既定のメソッドの実装を使う。

```anchor HonestFunctor
class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
  mapConst : {α β : Type u} → α → f β → f α :=
    Function.comp map (Function.const _)
```
この定義で{anchorName HonestFunctor}`Function.comp`は関数の合成であり、通常は{lit}`∘`演算子で書く。
{anchorName HonestFunctor}`Function.const`は*定数関数*で、二つ目の引数を無視する二引数の関数である。
この関数を一つの引数だけに適用すると、常に同じ値を返す関数ができる。APIが関数を要求するが、プログラムが引数ごとに違う結果を計算する必要がないときに役に立つ。
{anchorName HonestFunctor}`Function.const`の単純な版は次のように書ける。

```anchor simpleConst
def simpleConst  (x : α) (_ : β) : α := x
```
これを一つの引数とともに{anchorTerm extras}`List.map`の関数の引数として使うと、その有用性が分かる。
```anchor mapConst
#eval [1, 2, 3].map (simpleConst "same")
```
```anchorInfo mapConst
["same", "same", "same"]
```
実際の関数は次のシグネチャを持つ。
```anchorInfo FunctionConstType
Function.const.{u, v} {α : Sort u} (β : Sort v) (a : α) : β → α
```
ここで型引数{anchorName HonestFunctor}`β`は明示的な引数なので、{anchorName HonestFunctor}`mapConst`の既定の定義は{anchorTerm HonestFunctor}`_`の引数を与え、プログラムの型検査が通るような一意な型を{anchorName HonestFunctor}`Function.const`に渡すようLeanに指示する。
{anchorTerm unfoldCompConst}`Function.comp map (Function.const _)`は{anchorTerm unfoldCompConst}`fun (x : α) (y : f β) => map (fun _ => x) y`と等しい。

{anchorName HonestFunctor}`Functor`型クラスは、{anchorTerm HonestFunctor}`u+1`と{anchorTerm HonestFunctor}`v`の大きいほうの宇宙に属する。
ここで{anchorTerm HonestFunctor}`u`は{anchorName HonestFunctor}`f`の引数として受け付ける宇宙の段階であり、{anchorTerm HonestFunctor}`v`は{anchorName HonestFunctor}`f`が返す宇宙である。
{anchorName HonestFunctor}`Functor`型クラスを実装する構造体が{anchorTerm HonestFunctor}`u`より大きな宇宙にある必要がある理由を見るには、クラスの単純化した定義から始める。

```anchor FunctorSimplified
class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
```
この型クラスの構造体型は、次の帰納型と等しい。

```anchor FunctorDatatype
inductive Functor (f : Type u → Type v) : Type (max (u+1) v) where
  | mk : ({α β : Type u} → (α → β) → f α → f β) → Functor f
```
{anchorName FunctorDatatype}`mk`に引数として渡される{lit}`map`メソッドの実装には、{anchorTerm FunctorDatatype}`Type u`の型を二つ引数に取る関数が含まれる。
つまりその関数自体の型は{lit}`Type (u+1)`にあり、{anchorName FunctorDatatype}`Functor`も少なくとも{anchorTerm FunctorDatatype}`u+1`の段階になければならない。
同様に、その関数の他の引数の型は{anchorName FunctorDatatype}`f`を適用して作られるので、少なくとも{anchorTerm FunctorDatatype}`v`の段階でなければならない。
この節の型クラスはすべてこの性質を共有する。

# アプリカティブ
%%%
tag := "complete-applicative-definition"
%%%

{anchorName Applicative}`Applicative`型クラスは実際には、関係するメソッドをそれぞれいくつか含む多数の小さなクラスから組み立てられている。
まず{anchorName Applicative}`Pure`と{anchorName Applicative}`Seq`があり、それぞれ{anchorName Applicative}`pure`と{anchorName Seq}`seq`を含む。

```anchor Pure
class Pure (f : Type u → Type v) : Type (max (u+1) v) where
  pure {α : Type u} : α → f α
```

```anchor Seq
class Seq (f : Type u → Type v) : Type (max (u+1) v) where
  seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β
```

これらに加えて、{anchorName Applicative}`Applicative`は{anchorName SeqRight}`SeqRight`と、それに対応する{anchorName SeqLeft}`SeqLeft`クラスにも依存する。

```anchor SeqRight
class SeqRight (f : Type u → Type v) : Type (max (u+1) v) where
  seqRight : {α β : Type u} → f α → (Unit → f β) → f β
```

```anchor SeqLeft
class SeqLeft (f : Type u → Type v) : Type (max (u+1) v) where
  seqLeft : {α β : Type u} → f α → (Unit → f β) → f α
```

{ref "alternative"}[選択肢と検査についての節]で紹介した{anchorName SeqRight}`seqRight`関数は、副作用の観点から理解するのが最も簡単である。
{anchorTerm seqRightSugar (module := Examples.FunctorApplicativeMonad)}`E1 *> E2`は{anchorTerm seqRightSugar (module := Examples.FunctorApplicativeMonad)}`SeqRight.seqRight E1 (fun () => E2)`に脱糖され、まず{anchorName seqRightSugar (module:=Examples.FunctorApplicativeMonad)}`E1`を実行し、次に{anchorName seqRightSugar (module:=Examples.FunctorApplicativeMonad)}`E2`を実行して、{anchorName seqRightSugar (module:=Examples.FunctorApplicativeMonad)}`E2`の結果だけを返すものと理解できる。
{anchorName seqRightSugar (module:=Examples.FunctorApplicativeMonad)}`E1`の副作用によって、{anchorName seqRightSugar (module:=Examples.FunctorApplicativeMonad)}`E2`が実行されなかったり、複数回実行されたりすることがある。
実際、{anchorName SeqRight}`f`が{anchorName Monad}`Monad`インスタンスを持つなら、{anchorTerm seqRightSugar (module:=Examples.FunctorApplicativeMonad)}`E1 *> E2`は{lit}`do let _ ← E1; E2`と等しいが、{anchorName SeqRight}`seqRight`はモナドでない{anchorName Validate (module:=Examples.FunctorApplicativeMonad)}`Validate`のような型でも使える。

そのいとこである{anchorName SeqLeft}`seqLeft`もよく似ているが、最も左の式の値が返される点が異なる。
{anchorTerm seqLeftSugar}`E1 <* E2`は{anchorTerm seqLeftSugar}`SeqLeft.seqLeft E1 (fun () => E2)`に脱糖される。
{anchorTerm seqLeftType}`SeqLeft.seqLeft`の型は{anchorTerm seqLeftType}`f α → (Unit → f β) → f α`であり、{anchorTerm SeqLeft}`f α`を返す点を除けば{anchorName SeqRight}`seqRight`の型と同じである。
{anchorTerm seqLeftSugar}`E1 <* E2`は、まず{anchorName seqLeftSugar}`E1`を実行し、次に{anchorName seqLeftSugar}`E2`を実行して、{anchorName seqLeftSugar}`E1`の元の結果を返すプログラムと理解できる。
{anchorName SeqLeft}`f`が{anchorName Monad}`Monad`インスタンスを持つなら、{anchorTerm seqLeftSugar}`E1 <* E2`は{lit}`do let x ← E1; _ ← E2; pure x`と等しい。
一般に{anchorName SeqLeft}`seqLeft`は、検査や構文解析のような手順で、値自体を変えずにその値に追加の条件を課すのに役に立つ。

{anchorName Applicative}`Applicative`の定義は、{anchorName Applicative}`Functor`とともにこれらのクラスをすべて継承する。

```anchor Applicative
class Applicative (f : Type u → Type v)
    extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f where
  map      := fun x y => Seq.seq (pure x) fun _ => y
  seqLeft  := fun a b => Seq.seq (Functor.map (Function.const _) a) b
  seqRight := fun a b => Seq.seq (Functor.map (Function.const _ id) a) b
```
{anchorName Applicative}`Applicative`の完全な定義には、{anchorName Applicative}`pure`と{anchorName Seq}`seq`の定義だけが要る。
{anchorName Applicative}`Functor`、{anchorName SeqLeft}`SeqLeft`、{anchorName SeqRight}`SeqRight`のメソッドにはすべて既定の定義があるためである。
{anchorName HonestFunctor}`Functor`の{anchorName HonestFunctor}`mapConst`メソッドには、{anchorName Applicative}`Functor.map`を使った独自の既定の実装がある。
これらの既定の実装を上書きしてよいのは、振る舞いが等価でより効率のよい新しい関数に限る。
既定の実装は、自動で作られるコードであると同時に、正しさのための仕様とも見るべきである。

{anchorName SeqLeft}`seqLeft`の既定の実装はとても簡潔である。
一部の名前を糖衣構文や定義で置き換えると、別の見方が得られる。つまり、
```anchorTerm unfoldMapConstSeqLeft
Seq.seq (Functor.map (Function.const _) a) b
```
は次のようになる。
```anchorTerm unfoldMapConstSeqLeft
fun a b => Seq.seq ((fun x _ => x) <$> a) b
```
{anchorTerm unfoldMapConstSeqLeft}`(fun x _ => x) <$> a`はどう理解すべきだろうか。
ここで{anchorName unfoldMapConstSeqLeft}`a`の型は{anchorTerm unfoldMapConstSeqLeft}`f α`であり、{anchorName unfoldMapConstSeqLeft}`f`はファンクタである。
{anchorName unfoldMapConstSeqLeft}`f`が{anchorName extras}`List`なら、{anchorTerm mapConstList}`(fun x _ => x) <$> [1, 2, 3]`は{anchorTerm mapConstList}`[fun _ => 1, fun _ => 2, fun _ => 3`に評価される。
{anchorName unfoldMapConstSeqLeft}`f`が{anchorName mapConstOption}`Option`なら、{anchorTerm mapConstOption}`(fun x _ => x) <$> some "hello"`は{anchorTerm mapConstOption}`some (fun _ => "hello")`に評価される。
いずれの場合も、ファンクタの中の値が、引数を無視して元の値を返す関数に置き換えられる。
{anchorName Seq}`seq`と組み合わせると、この関数は{anchorName Seq}`seq`の二つ目の引数の値を捨てる。

{anchorName SeqRight}`seqRight`の既定の実装もよく似ているが、{anchorName FunctionConstType}`Function.const`に引数{anchorName Applicative}`id`がもう一つある点が異なる。
この定義も同様に、まず標準的な糖衣構文をいくつか導入し、次に一部の名前を定義で置き換えると理解できる。
```anchorEvalSteps unfoldMapConstSeqRight
fun a b => Seq.seq (Functor.map (Function.const _ id) a) b
===>
fun a b => Seq.seq ((fun _ => id) <$> a) b
===>
fun a b => Seq.seq ((fun _ => fun x => x) <$> a) b
===>
fun a b => Seq.seq ((fun _ x => x) <$> a) b
```
{anchorTerm unfoldMapConstSeqRight}`(fun _ x => x) <$> a`はどう理解すべきだろうか。
ここでもまた、例が役に立つ。
{anchorTerm mapConstIdList}`fun _ x => x) <$> [1, 2, 3]`は{anchorTerm mapConstIdList}`[fun x => x, fun x => x, fun x => x]`と等しく、{anchorTerm mapConstIdOption}`(fun _ x => x) <$> some "hello"`は{anchorTerm mapConstIdOption}`some (fun x => x)`と等しい。
言い換えれば、{anchorTerm unfoldMapConstSeqRight}`(fun _ x => x) <$> a`は{anchorName unfoldMapConstSeqRight}`a`の全体的な形を保つが、各値が恒等関数に置き換えられる。
副作用の観点では、{anchorName unfoldMapConstSeqRight}`a`の副作用は起きるが、{anchorName Seq}`seq`と組み合わせて使うと値は捨てられる。

# モナド
%%%
tag := "complete-monad-definition"
%%%

{anchorName Applicative}`Applicative`を構成する操作がそれぞれ独自の型クラスに分かれているのと同じように、{anchorName Bind}`Bind`にも独自のクラスがある。

```anchor Bind
class Bind (m : Type u → Type v) where
  bind : {α β : Type u} → m α → (α → m β) → m β
```
{anchorName Monad}`Monad`は{anchorName Applicative}`Applicative`を{anchorName Bind}`Bind`で拡張する。

```anchor Monad
class Monad (m : Type u → Type v) : Type (max (u+1) v)
    extends Applicative m, Bind m where
  map      f x := bind x (Function.comp pure f)
  seq      f x := bind f fun y => Functor.map y (x ())
  seqLeft  x y := bind x fun a => bind (y ()) (fun _ => pure a)
  seqRight x y := bind x fun _ => y ()
```
階層全体から継承したメソッドと既定のメソッドの集まりをたどると、{anchorName Monad}`Monad`インスタンスには{anchorName Bind}`bind`と{anchorName Pure}`pure`の実装だけが要ることが分かる。
言い換えれば、{anchorName Monad}`Monad`インスタンスは{anchorName Seq}`seq`、{anchorName SeqLeft}`seqLeft`、{anchorName SeqRight}`seqRight`、{anchorName HonestFunctor}`map`、{anchorName HonestFunctor}`mapConst`の実装を自動で与える。
APIの境界という観点では、{anchorName Monad}`Monad`インスタンスを持つ型は{anchorName Bind}`Bind`、{anchorName Pure}`Pure`、{anchorName Seq}`Seq`、{anchorName Applicative}`Functor`、{anchorName SeqLeft}`SeqLeft`、{anchorName SeqRight}`SeqRight`のインスタンスも得る。


# 練習問題
%%%
tag := "complete-functor-applicative-monad-exercises"
%%%

 1. {anchorName mapConstOption}`Option`や{anchorName ApplicativeExcept (module:=Examples.FunctorApplicativeMonad)}`Except`のような例を具体的に解いて、{anchorName Monad}`Monad`における{anchorName HonestFunctor}`map`、{anchorName Seq}`seq`、{anchorName SeqLeft}`seqLeft`、{anchorName SeqRight}`seqRight`の既定の実装を理解せよ。言い換えれば、{anchorName Bind}`bind`と{anchorName Pure}`pure`の定義を既定の定義に代入し、簡約して、手で書くであろう{anchorName HonestFunctor}`map`、{anchorName Seq}`seq`、{anchorName SeqLeft}`seqLeft`、{anchorName SeqRight}`seqRight`の版を取り戻せ。
 2. 紙の上かテキストファイルで、{anchorName HonestFunctor}`map`と{anchorName Seq}`seq`の既定の実装が{anchorName Applicative}`Functor`と{anchorName Applicative}`Applicative`の契約を満たすことを自分に納得させよ。この議論では、{anchorName Monad}`Monad`の契約の規則と、普通の式の評価を使ってよい。
