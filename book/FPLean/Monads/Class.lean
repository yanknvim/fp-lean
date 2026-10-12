module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads.Class"

#doc (Manual) "The Monad Type Class" =>
%%%
tag := "monad-type-class"
%%%

:::paragraph
モナドである型ごとに{lit}`ok`や{lit}`andThen`のような演算子を import しなくてもよいように、Leanの標準ライブラリにはこれらをオーバーロードする型クラスがあり、同じ演算子を*どの*モナドにも使える。
モナドには二つの操作があり、{lit}`ok`と{lit}`andThen`に相当する。

```anchor FakeMonad
class Monad (m : Type → Type) where
  pure : α → m α
  bind : m α → (α → m β) → m β
```
この定義は少し単純化してある。
Leanのライブラリにある実際の定義はもう少し込み入っており、後で示す。
:::

:::paragraph
{anchorName MonadOptionExcept}`Option`と{anchorTerm MonadOptionExcept}`Except ε`の{anchorName MonadOptionExcept}`Monad`インスタンスは、それぞれの{lit}`andThen`の定義を手直しして作れる。

```anchor MonadOptionExcept
instance : Monad Option where
  pure x := some x
  bind opt next :=
    match opt with
    | none => none
    | some x => next x

instance : Monad (Except ε) where
  pure x := Except.ok x
  bind attempt next :=
    match attempt with
    | Except.error e => Except.error e
    | Except.ok x => next x
```
:::

:::paragraph
例として、{lit}`firstThirdFifthSeventh`は{anchorTerm Names}`Option α`と{anchorTerm Names}`Except String α`の戻り値の型それぞれについて別々に定義していた。
今度は、*どの*モナドについても多相的に定義できる。
ただし、参照の関数を引数に取る必要がある。モナドによって結果を見つけられないときの振る舞いが異なりうるためである。
{anchorName FakeMonad}`bind`の中置版は{lit}`>>=`であり、例における{lit}`~~>`と同じ役割を果たす。

```anchor firstThirdFifthSeventhMonad
def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α)
    (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)
```
:::

:::paragraph
遅い哺乳類と速い鳥の例のリストがあれば、この{anchorName firstThirdFifthSeventhMonad}`firstThirdFifthSeventh`の実装は{moduleName}`Option`で使える。

```anchor animals
def slowMammals : List String :=
  ["Three-toed sloth", "Slow loris"]

def fastBirds : List String := [
  "Peregrine falcon",
  "Saker falcon",
  "Golden eagle",
  "Gray-headed albatross",
  "Spur-winged goose",
  "Swift",
  "Anna's hummingbird"
]
```
```anchor noneSlow
#eval firstThirdFifthSeventh (fun xs i => xs[i]?) slowMammals
```
```anchorInfo noneSlow
none
```
```anchor someFast
#eval firstThirdFifthSeventh (fun xs i => xs[i]?) fastBirds
```
```anchorInfo someFast
some ("Peregrine falcon", "Golden eagle", "Spur-winged goose", "Anna's hummingbird")
```
:::

:::paragraph
{anchorName getOrExcept}`Except`の参照の関数{lit}`get`をより具体的な名前に変えれば、まったく同じ{anchorName firstThirdFifthSeventhMonad}`firstThirdFifthSeventh`の実装を{anchorName getOrExcept}`Except`でも使える。

```anchor getOrExcept
def getOrExcept (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none =>
    Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x =>
    Except.ok x
```
```anchor errorSlow
#eval firstThirdFifthSeventh getOrExcept slowMammals
```
```anchorInfo errorSlow
Except.error "Index 2 not found (maximum is 1)"
```
```anchor okFast
#eval firstThirdFifthSeventh getOrExcept fastBirds
```
```anchorInfo okFast
Except.ok ("Peregrine falcon", "Golden eagle", "Spur-winged goose", "Anna's hummingbird")
```
{anchorName firstThirdFifthSeventhMonad}`m`が{anchorName firstThirdFifthSeventhMonad}`Monad`インスタンスを持たなければならないということは、{lit}`>>=`と{anchorName firstThirdFifthSeventhMonad}`pure`の操作が使えるということである。
:::

# 一般的なモナドの操作
%%%
tag := "monad-class-polymorphism"
%%%

:::paragraph
多くの異なる型がモナドなので、*どの*モナドについても多相的な関数はとても強力である。
たとえば{anchorName mapM}`mapM`関数は{anchorName Names (show:=map)}`Functor.map`の一種で、{anchorName mapM}`Monad`を使って関数を適用した結果をつなげてまとめる。

```anchor mapM
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM f xs >>= fun tl =>
    pure (hd :: tl)
```
引数の関数{anchorName mapM}`f`の戻り値の型が、どの{anchorName mapM}`Monad`インスタンスを使うかを決める。
言い換えれば、{anchorName mapM}`mapM`はログを作る関数にも、失敗しうる関数にも、可変状態を使う関数にも使える。
{anchorName mapM}`f`の型が使える副作用を決めるので、APIの設計者はそれを厳密に制御できる。
:::

:::paragraph
{ref "numbering-tree-nodes"}[この章の導入]で述べたように、{anchorTerm StateEx}`State σ α`は型{anchorName StateEx}`σ`の可変変数を使い、型{anchorName StateEx}`α`の値を返すプログラムを表す。
これらのプログラムは実際には、開始時の状態から、値と最終状態の組への関数である。
{anchorName StateMonad}`Monad`クラスは、その引数が型の引数を一つ取ることを要求する。つまり{anchorTerm StateEx}`Type → Type`でなければならない。
そのため{anchorName StateMonad}`State`のインスタンスは状態の型{anchorName StateMonad}`σ`に言及する必要があり、それがインスタンスの引数になる。

```anchor StateMonad
instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'
```
つまり、{anchorName StateMonad}`bind`でつなげた{anchorName StateEx}`get`と{anchorName StateEx}`set`の呼び出しの間で状態の型は変えられない。これは状態を使う計算としては妥当な規則である。
{anchorName increment}`increment`演算子は、保存された状態を与えられた量だけ増やし、古い値を返す。

```anchor increment
def increment (howMuch : Int) : State Int Int :=
  get >>= fun i =>
  set (i + howMuch) >>= fun () =>
  pure i
```
:::

:::paragraph
{anchorName mapMincrementOut}`mapM`を{anchorName mapMincrementOut}`increment`と組み合わせると、リストの要素の和を計算するプログラムになる。
より具体的には、可変変数にはそこまでの和が入り、結果のリストには累積和が入る。
言い換えれば、{anchorTerm mapMincrement}`mapM increment`の型は{anchorTerm mapMincrement}`List Int → State Int (List Int)`であり、{anchorName StateMonad}`State`の定義を展開すると{anchorTerm mapMincrement2}`List Int → Int → (Int × List Int)`になる。
初期の和を引数に取る。ここでは{anchorTerm mapMincrementOut}`0`とすればよい。
```anchor mapMincrementOut
#eval mapM increment [1, 2, 3, 4, 5] 0
```
```anchorInfo mapMincrementOut
(15, [0, 1, 3, 6, 10])
```
:::

:::paragraph
{ref "logging"}[ログの副作用]は{anchorName MonadWriter}`WithLog`で表せる。
{anchorName StateEx}`State`と同じく、その{anchorName MonadWriter}`Monad`インスタンスは記録するデータの型について多相的である。

```anchor MonadWriter
instance : Monad (WithLog logged) where
  pure x := {log := [], val := x}
  bind result next :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}
```
:::

:::paragraph
{anchorName saveIfEven}`saveIfEven`は、偶数をログに記録するが引数は変えずに返す関数である。

```anchor saveIfEven
def saveIfEven (i : Int) : WithLog Int Int :=
  (if isEven i then
    save i
   else pure ()) >>= fun () =>
  pure i
```
この関数を{anchorName mapMsaveIfEven}`mapM`と組み合わせると、偶数を含むログと、変わっていない入力のリストが組になる。
```anchor mapMsaveIfEven
#eval mapM saveIfEven [1, 2, 3, 4, 5]
```
```anchorInfo mapMsaveIfEven
{ log := [2, 4], val := [1, 2, 3, 4, 5] }
```
:::


# 恒等モナド
%%%
tag := "Id-monad"
%%%

モナドは、失敗や例外、ログといった副作用を持つプログラムを、データと関数による明示的な表現に符号化する。
しかし、柔軟さのためにモナドを使うAPIが書かれる一方で、そのAPIの利用者にとって符号化された副作用がまったく要らないこともある。
{deftech}*恒等モナド*は副作用を持たないモナドである。
これにより、純粋なコードをモナドを使うAPIで使える。

```anchor IdMonad
def Id (t : Type) : Type := t

instance : Monad Id where
  pure x := x
  bind x f := f x
```
{anchorName IdMonad}`pure`の型は{anchorTerm IdMore}`α → Id α`であるべきだが、{anchorTerm IdMore}`Id α`は{anchorTerm IdMore}`α`に簡約される。
同様に、{anchorName IdMonad}`bind`の型は{anchorTerm IdMore}`α → (α → Id β) → Id β`であるべきである。
これが{anchorTerm IdMore}`α → (α → β) → β`に簡約されるので、二つ目の引数を一つ目に適用すれば結果が得られる。

:::paragraph
恒等モナドを使うと、{anchorName mapMId}`mapM`は{anchorName Names (show:=map)}`Functor.map`と同じになる。
ただしこのように呼び出すには、意図するモナドが{anchorName mapMId}`Id`であるという手がかりをLeanに与える必要がある。
```anchor mapMId
def numbers := mapM (m := Id) (do return · + 1) [1, 2, 3, 4, 5]
```
どのモナドを使うかについて型が何の手がかりも与えない文脈で{anchorName mapMIdId}`mapM`を使うと、「インスタンスの問題が行き詰まった」というメッセージになる。
```anchor mapMIdId
def numbers := mapM (do return · + 1) [1, 2, 3, 4, 5]
```
```anchorError mapMIdId
typeclass instance problem is stuck
  Pure ?m.6

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Pure` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
```
:::

# モナドの契約
%%%
tag := "monad-contract"
%%%

{anchorName MonadContract}`BEq`と{anchorName MonadContract}`Hashable`のインスタンスの組が、等しい二つの値のハッシュが同じになることを保証すべきであるのと同じように、{anchorName MonadContract}`Monad`の各インスタンスが守るべき契約がある。
第一に、{anchorName MonadContract}`pure`は{anchorName MonadContract}`bind`の左単位元であるべきである。
つまり、{anchorTerm MonadContract}`bind (pure v) f`は{anchorTerm MonadContract}`f v`と同じであるべきである。
第二に、{anchorName MonadContract}`pure`は{anchorName MonadContract}`bind`の右単位元であるべきであり、{anchorTerm MonadContract}`bind v pure`は{anchorName MonadContract2}`v`と同じである。
最後に、{anchorName MonadContract}`bind`は結合的であるべきであり、{anchorTerm MonadContract}`bind (bind v f) g`は{anchorTerm MonadContract}`bind v (fun x => bind (f x) g)`と同じである。

この契約は、副作用を持つプログラムに期待される性質をより一般に定めている。
{anchorName MonadContract}`pure`には副作用がないので、{anchorName MonadContract}`bind`でつなげても結果は変わらないはずである。
{anchorName MonadContract}`bind`の結合性は、起こる事柄の順序が保たれていれば、つなげ方の段取り自体は問題にならない、ということをおおよそ述べている。

# 練習問題
%%%
tag := "monad-class-exercises"
%%%

## 木のマップ
%%%
tag := none
%%%

:::paragraph
{anchorName ex1}`BinTree.mapM`関数を定義せよ。
リストの{anchorName mapM}`mapM`にならって、この関数は木の各データに関数を適用するものとし、先行順でたどる。
型シグネチャは次のとおりとする。
```anchorTerm ex1
def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
```
:::

## Optionのモナド契約
%%%
tag := none
%%%

:::paragraph
まず、{anchorName badOptionMonad}`Option`の{anchorName badOptionMonad}`Monad`インスタンスがモナドの契約を満たすことを、説得力のある議論で示せ。
次に、次のインスタンスを考えよ。
```anchor badOptionMonad
instance : Monad Option where
  pure x := some x
  bind opt next := none
```
どちらのメソッドも型は正しい。
このインスタンスはなぜモナドの契約に反するのか。
:::
