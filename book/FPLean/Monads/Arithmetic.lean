module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads.Class"

#doc (Manual) "Example: Arithmetic in Monads" =>
%%%
tag := "monads-arithmetic-example"
%%%

モナドは、副作用を持つプログラムを、副作用を持たない言語に符号化する手段である。
これを、純粋な関数型プログラムには何か重要なものが欠けており、普通のプログラムを書くだけでもプログラマが面倒な手順を踏まされる、という告白のように読むのはたやすい。
しかし、{moduleName}`Monad`のAPIを使うとプログラムに構文上の負担がかかるものの、二つの重要な利点がある。
 1. プログラムは、どの副作用を使うかを型に正直に書かねばならない。型シグネチャをちらりと見るだけで、そのプログラムが受け取るものと返すものだけでなく、*できることのすべて*が分かる。
 2. どの言語も同じ副作用を備えているわけではない。たとえば例外を持つ言語は一部だけである。他の言語には、[Iconの複数の値の探索](https://www2.cs.arizona.edu/icon/)やSchemeやRubyの継続のように、独特で風変わりな副作用がある。モナドは*どんな*副作用でも符号化できるので、プログラマは言語の開発者が用意したものに縛られることなく、用途に最も合うものを選べる。

さまざまなモナドで意味をなすプログラムの例として、算術式の評価器がある。

# 算術式
%%%
tag := "monads-arithmetic-example-expr"
%%%

:::paragraph
算術式は、整数のリテラルか、二つの式に適用する原始的な二項演算子のどちらかである。演算子は加算、減算、乗算、除算である。

```anchor ExprArith
inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op


inductive Arith where
  | plus
  | minus
  | times
  | div
```
:::

:::paragraph
式{lit}`2 + 3`は次のように表される。

```anchor twoPlusThree
open Expr in
open Arith in
def twoPlusThree : Expr Arith :=
  prim plus (const 2) (const 3)
```
また{lit}`14 / (45 - 5 * 9)`は次のように表される。
```anchor exampleArithExpr
open Expr in
open Arith in
def fourteenDivided : Expr Arith :=
  prim div (const 14)
    (prim minus (const 45)
      (prim times (const 5)
        (const 9)))
```
:::

# 式の評価
%%%
tag := "monads-arithmetic-example-eval"
%%%

:::paragraph
式には除算があり、ゼロによる除算は定義されないので、評価は失敗しうる。
失敗を表す一つの方法は{anchorName evaluateOptionCommingled}`Option`を使うことである。

```anchor evaluateOptionCommingled
def evaluateOption : Expr Arith → Option Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateOption e1 >>= fun v1 =>
    evaluateOption e2 >>= fun v2 =>
    match p with
    | Arith.plus => pure (v1 + v2)
    | Arith.minus => pure (v1 - v2)
    | Arith.times => pure (v1 * v2)
    | Arith.div => if v2 == 0 then none else pure (v1 / v2)
```
:::

:::paragraph
この定義は{anchorTerm MonadOptionExcept}`Monad Option`インスタンスを使い、二項演算子の両方の枝を評価したときの失敗を伝播させる。
しかしこの関数は、二つの関心事を混ぜている。部分式を評価することと、その結果に二項演算子を適用することである。
二つの関数に分ければよくなる。

```anchor evaluateOptionSplit
def applyPrim : Arith → Int → Int → Option Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => if y == 0 then none else pure (x / y)

def evaluateOption : Expr Arith → Option Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateOption e1 >>= fun v1 =>
    evaluateOption e2 >>= fun v2 =>
    applyPrim p v1 v2
```
:::

:::paragraph
{anchorTerm fourteenDivOption}`#eval evaluateOption fourteenDivided`を実行すると予想どおり{anchorInfo fourteenDivOption}`none`になるが、これはあまり役に立つエラーメッセージではない。
コードが{anchorName MonadOptionExcept}`none`コンストラクタを明示的に扱うのではなく{lit}`>>=`を使って書かれているので、失敗時にエラーメッセージを出すようにするには少し手直しするだけでよい。

```anchor evaluateExcept
def applyPrim : Arith → Int → Int → Except String Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def evaluateExcept : Expr Arith → Except String Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateExcept e1 >>= fun v1 =>
    evaluateExcept e2 >>= fun v2 =>
    applyPrim p v1 v2
```
違いは、型シグネチャが{anchorName Names}`Option`ではなく{anchorTerm evaluateExcept}`Except String`に言及していることと、失敗する場合に{anchorName evaluateM}`none`ではなく{anchorName evaluateExcept}`Except.error`を使っていることだけである。
評価器をそのモナドについて多相的にし、{anchorName evaluateM}`applyPrim`を引数として渡せば、一つの評価器が両方の形のエラー報告に対応できる。

```anchor evaluateM
def applyPrimOption : Arith → Int → Int → Option Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y =>
    if y == 0 then
      none
    else pure (x / y)

def applyPrimExcept : Arith → Int → Int → Except String Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def evaluateM [Monad m]
    (applyPrim : Arith → Int → Int → m Int) :
    Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applyPrim e1 >>= fun v1 =>
    evaluateM applyPrim e2 >>= fun v2 =>
    applyPrim p v1 v2
```
:::

{anchorName evaluateMOption}`applyPrimOption`と組み合わせると、最初の評価器と同じように動く。
```anchor evaluateMOption
#eval evaluateM applyPrimOption fourteenDivided
```
```anchorInfo evaluateMOption
none
```
同様に、{anchorName evaluateMExcept}`applyPrimExcept`と組み合わせると、エラーメッセージ付きの版と同じように動く。
```anchor evaluateMExcept
#eval evaluateM applyPrimExcept fourteenDivided
```
```anchorInfo evaluateMExcept
Except.error "Tried to divide 14 by zero"
```

:::paragraph
このコードはまだよくできる。
{anchorName evaluateMOption}`applyPrimOption`と{anchorName evaluateMExcept}`applyPrimExcept`の違いは除算の扱いだけであり、それは評価器のもう一つの引数としてくくり出せる。

```anchor evaluateMRefactored
def applyDivOption (x : Int) (y : Int) : Option Int :=
    if y == 0 then
      none
    else pure (x / y)

def applyDivExcept (x : Int) (y : Int) : Except String Int :=
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrim [Monad m]
    (applyDiv : Int → Int → m Int) :
    Arith → Int → Int → m Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => applyDiv x y

def evaluateM [Monad m]
    (applyDiv : Int → Int → m Int) :
    Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applyDiv e1 >>= fun v1 =>
    evaluateM applyDiv e2 >>= fun v2 =>
    applyPrim applyDiv p v1 v2
```

この手直ししたコードでは、二つの道筋の違いが失敗の扱いだけであることが完全に明らかになっている。
:::

# さらなる副作用
%%%
tag := "monads-arithmetic-example-effects"
%%%

評価器を扱うときに興味深い副作用は、失敗と例外だけではない。
除算の副作用は失敗だけだが、式に他の原始的な演算子を加えると、他の副作用を表せるようになる。

まず、もう一段の手直しとして、除算を原始的な演算子のデータ型からくくり出す。

```anchor PrimCanFail
inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special

inductive CanFail where
  | div
```
{anchorName PrimCanFail}`CanFail`という名前は、除算が持ち込む副作用が失敗の可能性であることを示唆している。

次に、{anchorName evaluateMMorePoly}`evaluateM`の除算の処理を担う引数の範囲を広げ、任意の特別な演算子を処理できるようにする。

```anchor evaluateMMorePoly
def divOption : CanFail → Int → Int → Option Int
  | CanFail.div, x, y => if y == 0 then none else pure (x / y)

def divExcept : CanFail → Int → Int → Except String Int
  | CanFail.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrim [Monad m]
    (applySpecial : special → Int → Int → m Int) :
    Prim special → Int → Int → m Int
  | Prim.plus, x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.other op, x, y => applySpecial op x y

def evaluateM [Monad m]
    (applySpecial : special → Int → Int → m Int) :
    Expr (Prim special) → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applySpecial e1 >>= fun v1 =>
    evaluateM applySpecial e2 >>= fun v2 =>
    applyPrim applySpecial p v1 v2
```

## 副作用なし
%%%
tag := "monads-arithmetic-example-no-effects"
%%%

{anchorName applyEmpty}`Empty`型にはコンストラクタがなく、したがって値もない。ScalaやKotlinの{Kotlin}`Nothing`型のようなものである。
ScalaやKotlinでは、{Kotlin}`Nothing`は結果を返すことのない計算を表せる。プログラムを落としたり例外を投げたり常に無限ループに陥ったりする関数である。
型{Kotlin}`Nothing`の関数やメソッドの引数は、適切な引数の値が決して存在しないので、到達しないコードを示す。
Leanは無限ループと例外を扱えないが、{anchorName applyEmpty}`Empty`は、その関数が呼べないことを型システムに示すのに今でも役に立つ。
型にコンストラクタがない式{anchorName nomatch}`E`に対して{anchorTerm nomatch}`nomatch E`という構文を使うと、その式は決して呼ばれえないので結果を返す必要がないことをLeanに示せる。

{anchorName PrimCanFail}`Prim`の引数に{anchorName applyEmpty}`Empty`を使うと、{anchorName evaluateMMorePoly}`Prim.plus`、{anchorName evaluateMMorePoly}`Prim.minus`、{anchorName evaluateMMorePoly}`Prim.times`以外の場合はないことが示される。{anchorName evaluateMMorePoly}`Prim.other`コンストラクタに入れる型{anchorName nomatch}`Empty`の値が考えられないためである。
型{anchorName nomatch}`Empty`の演算子を二つの整数に適用する関数は決して呼べないので、結果を返す必要がない。
したがって、*どの*モナドでも使える。

```anchor applyEmpty
def applyEmpty [Monad m] (op : Empty) (_ : Int) (_ : Int) : m Int :=
  nomatch op
```
これを恒等モナドである{anchorName evalId}`Id`と組み合わせると、副作用がまったくない式を評価できる。
```anchor evalId
open Expr Prim in
#eval evaluateM (m := Id) applyEmpty (prim plus (const 5) (const (-14)))
```
```anchorInfo evalId
-9
```

## 非決定的な探索
%%%
tag := "nondeterministic-search"
%%%

ゼロによる除算に出会ったときに単に失敗するのではなく、後戻りして別の入力を試すのももっともである。
適切なモナドがあれば、まったく同じ{anchorName evalId}`evaluateM`で、失敗しない*集合*の答えを非決定的に探索できる。
そのためには除算に加えて、結果の選択を指定する手段が要る。
その一つの方法は、式の言語に{lit}`choose`という関数を加え、失敗しない結果を探すときにそのどちらかの引数を選ぶよう評価器に指示することである。

評価器の結果は、単一の値ではなく値の多重集合になる。
多重集合への評価の規則は次のとおりである。
 * 定数$`n`は単元集合$`\{n\}`に評価される。
 * 除算以外の算術演算子は、演算子の直積の各組に対して呼ばれる。したがって$`X + Y`は$`\{ x + y \mid x ∈ X, y ∈ Y \}`に評価される。
 * 除算$`X / Y`は$`\{ x / y \mid x ∈ X, y ∈ Y, y ≠ 0\}`に評価される。言い換えれば、$`Y`にある$`0`の値はすべて捨てられる。
 * 選択$`\mathrm{choose}(x, y)`は$`\{ x, y \}`に評価される。

たとえば$`1 + \mathrm{choose}(2, 5)`は$`\{ 3, 6 \}`に、$`1 + 2 / 0`は$`\{\}`に、$`90 / (\mathrm{choose}(-5, 5) + 5)`は$`\{ 9 \}`に評価される。
真の集合ではなく多重集合を使うと、要素の一意性を調べる必要がなくなり、コードが簡単になる。

:::paragraph
この非決定的な副作用を表すモナドは、答えがまったくない状況と、少なくとも一つの答えと残りの答えがある状況を表せる必要がある。

```anchor Many (module := Examples.Monads.Many)
inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α
```
このデータ型は{anchorName fromList (module:=Examples.Monads.Many)}`List`にとてもよく似ている。
違いは、{anchorName etc}`List.cons`がリストの残りを保持するのに対し、{anchorName Many (module:=Examples.Monads.Many)}`more`は残りの値を必要になったときに計算する関数を保持する点である。
つまり、{anchorName Many (module:=Examples.Monads.Many)}`Many`の利用側は、いくつかの結果が見つかったところで探索を止められる。
:::

:::paragraph
単一の結果は、それ以上結果を返さない{anchorName Many (module:=Examples.Monads.Many)}`more`コンストラクタで表す。

```anchor one (module := Examples.Monads.Many)
def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)
```
:::

:::paragraph
結果の二つの多重集合の和は、一つ目の多重集合が空かどうかを調べることで計算できる。
空なら、二つ目の多重集合が和である。
空でなければ、和は、一つ目の多重集合の最初の要素の後に、一つ目の多重集合の残りと二つ目の多重集合の和を続けたものである。

```anchor union (module := Examples.Monads.Many)
def Many.union : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)
```
:::

:::paragraph
探索の過程を値のリストから始められると便利である。
{anchorName fromList (module:=Examples.Monads.Many)}`Many.fromList`はリストを結果の多重集合に変換する。

```anchor fromList (module := Examples.Monads.Many)
def Many.fromList : List α → Many α
  | [] => Many.none
  | x :: xs => Many.more x (fun () => fromList xs)
```

同様に、探索を指定した後は、いくつかの値だけを取り出したり、すべての値を取り出したりできると便利である。

```anchor take (module := Examples.Monads.Many)
def Many.take : Nat → Many α → List α
  | 0, _ => []
  | _ + 1, Many.none => []
  | n + 1, Many.more x xs => x :: (xs ()).take n

def Many.takeAll : Many α → List α
  | Many.none => []
  | Many.more x xs => x :: (xs ()).takeAll
```
:::

{anchorTerm MonadMany (module:=Examples.Monads.Many)}`Monad Many`インスタンスには{anchorName MonadContract}`bind`演算子が要る。
非決定的な探索では、二つの操作をつなげるとは、一つ目の段階からすべての可能性を取り、それぞれについてプログラムの残りを実行し、その結果の和を取ることである。
言い換えれば、一つ目の段階が三つの答えを返しうるなら、二つ目の段階をその三つすべてについて試す必要がある。
二つ目の段階は入力ごとにいくつの答えでも返しうるので、その和を取ることが探索空間の全体を表す。

```anchor bind (module := Examples.Monads.Many)
def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ =>
    Many.none
  | Many.more x xs, f =>
    (f x).union (bind (xs ()) f)
```

{anchorName MonadMany (module:=Examples.Monads.Many)}`Many.one`と{anchorName MonadMany (module:=Examples.Monads.Many)}`Many.bind`はモナドの契約を満たす。
{anchorTerm bindLeft (module:=Examples.Monads.Many)}`Many.bind (Many.one v) f`が{anchorTerm bindLeft (module:=Examples.Monads.Many)}`f v`と同じであることを確かめるには、まず式をできるところまで評価する。
```anchorEvalSteps bindLeft (module := Examples.Monads.Many)
Many.bind (Many.one v) f
===>
Many.bind (Many.more v (fun () => Many.none)) f
===>
(f v).union (Many.bind Many.none f)
===>
(f v).union Many.none
```
空の多重集合は{anchorName union (module:=Examples.Monads.Many)}`union`の右単位元なので、答えは{anchorTerm bindLeft (module:=Examples.Monads.Many)}`f v`と等しい。
{anchorTerm bindOne (module:=Examples.Monads.Many)}`Many.bind v Many.one`が{anchorName bindOne (module:=Examples.Monads.Many)}`v`と同じであることを確かめるには、{anchorName bindOne (module:=Examples.Monads.Many)}`Many.bind`が{anchorName bindOne (module:=Examples.Monads.Many)}`v`の各要素に{anchorName one (module:=Examples.Monads.Many)}`Many.one`を適用したものの和を取ることを考えればよい。
言い換えれば、{anchorName bindOne (module:=Examples.Monads.Many)}`v`が{anchorTerm vSet (module:=Examples.Monads.Many)}`{v₁, v₂, v₃, …, vₙ}`の形なら、{anchorTerm bindOne (module:=Examples.Monads.Many)}`Many.bind v Many.one`は{anchorTerm vSets (module:=Examples.Monads.Many)}`{v₁} ∪ {v₂} ∪ {v₃} ∪ … ∪ {vₙ}`であり、これは{anchorTerm vSet (module:=Examples.Monads.Many)}`{v₁, v₂, v₃, …, vₙ}`である。

最後に、{anchorName bind (module:=Examples.Monads.Many)}`Many.bind`が結合的であることを確かめるには、{anchorTerm bindBindLeft (module:=Examples.Monads.Many)}`Many.bind (Many.bind v f) g`が{anchorTerm bindBindRight (module:=Examples.Monads.Many)}`Many.bind v (fun x => Many.bind (f x) g)`と同じであることを確かめる。
{anchorName bindBindRight (module:=Examples.Monads.Many)}`v`が{anchorTerm vSet (module:=Examples.Monads.Many)}`{v₁, v₂, v₃, …, vₙ}`の形なら、次のようになる。
```anchorEvalSteps bindUnion (module := Examples.Monads.Many)
Many.bind v f
===>
f v₁ ∪ f v₂ ∪ f v₃ ∪ … ∪ f vₙ
```
したがって次のようになる。
```anchorEvalSteps bindBindLeft (module := Examples.Monads.Many)
Many.bind (Many.bind v f) g
===>
Many.bind (f v₁) g ∪
Many.bind (f v₂) g ∪
Many.bind (f v₃) g ∪
… ∪
Many.bind (f vₙ) g
```
同様に、
```anchorEvalSteps bindBindRight (module := Examples.Monads.Many)
Many.bind v (fun x => Many.bind (f x) g)
===>
(fun x => Many.bind (f x) g) v₁ ∪
(fun x => Many.bind (f x) g) v₂ ∪
(fun x => Many.bind (f x) g) v₃ ∪
… ∪
(fun x => Many.bind (f x) g) vₙ
===>
Many.bind (f v₁) g ∪
Many.bind (f v₂) g ∪
Many.bind (f v₃) g ∪
… ∪
Many.bind (f vₙ) g
```
これで両辺が等しいので、{anchorName bindAssoc (module:=Examples.Monads.Many)}`Many.bind`は結合的である。

得られるモナドのインスタンスは次のとおりである。

```anchor MonadMany (module := Examples.Monads.Many)
instance : Monad Many where
  pure := Many.one
  bind := Many.bind
```
このモナドを使った探索の例として、リストにある数のうち和が15になる組み合わせをすべて見つけるものがある。

```anchor addsTo (module := Examples.Monads.Many)
def addsTo (goal : Nat) : List Nat → Many (List Nat)
  | [] =>
    if goal == 0 then
      pure []
    else
      Many.none
  | x :: xs =>
    if x > goal then
      addsTo goal xs
    else
      (addsTo goal xs).union
        (addsTo (goal - x) xs >>= fun answer =>
         pure (x :: answer))
```
探索の過程はリストについて再帰的である。
空のリストは、目標が{anchorTerm addsTo (module:=Examples.Monads.Many)}`0`のときは成功する探索であり、そうでなければ失敗する。
リストが空でないときは二つの可能性がある。リストの先頭が目標より大きい場合は、どの成功する探索にも加われない。そうでない場合は加われる。
リストの先頭が候補で*ない*なら、探索はリストの残りに進む。
先頭が候補なら、{anchorName union (module:=Examples.Monads.Many)}`Many.union`でまとめるべき二つの可能性がある。見つかった解が先頭を含むか、含まないかである。
先頭を含まない解はリストの残りへの再帰呼び出しで見つかり、先頭を含む解は、目標から先頭を引いて、その再帰呼び出しで得られる解の先頭にその要素を付けたものである。

補助関数{anchorName printList (module:=Examples.Monads.Many)}`printList`は、結果を一行に一つずつ表示する。

```anchor printList (module := Examples.Monads.Many)
def printList [ToString α] : List α → IO Unit
  | [] => pure ()
  | x :: xs => do
    IO.println x
    printList xs
```
```anchor addsToFifteen (module := Examples.Monads.Many)
#eval printList (addsTo 15 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]).takeAll
```
```anchorInfo addsToFifteen (module := Examples.Monads.Many)
[7, 8]
[6, 9]
[5, 10]
[4, 5, 6]
[3, 5, 7]
[3, 4, 8]
[2, 6, 7]
[2, 5, 8]
[2, 4, 9]
[2, 3, 10]
[2, 3, 4, 6]
[1, 6, 8]
[1, 5, 9]
[1, 4, 10]
[1, 3, 5, 6]
[1, 3, 4, 7]
[1, 2, 5, 7]
[1, 2, 4, 8]
[1, 2, 3, 9]
[1, 2, 3, 4, 5]
```

:::paragraph
結果の多重集合を作る算術の評価器に戻ると、{anchorName NeedsSearch}`choose`演算子で値を非決定的に選べ、ゼロによる除算はそれまでの選択を無効にする。

```anchor NeedsSearch
inductive NeedsSearch
  | div
  | choose

def applySearch : NeedsSearch → Int → Int → Many Int
  | NeedsSearch.choose, x, y =>
    Many.fromList [x, y]
  | NeedsSearch.div, x, y =>
    if y == 0 then
      Many.none
    else Many.one (x / y)
```
:::

:::paragraph
これらの演算子を使うと、先ほどの例を評価できる。

```anchor opening
open Expr Prim NeedsSearch
```
```anchor searchA
#eval
  (evaluateM applySearch
    (prim plus (const 1)
      (prim (other choose) (const 2)
        (const 5)))).takeAll
```
```anchorInfo searchA
[3, 6]
```
```anchor searchB
#eval
  (evaluateM applySearch
    (prim plus (const 1)
      (prim (other div) (const 2)
        (const 0)))).takeAll
```
```anchorInfo searchB
[]
```
```anchor searchC
#eval
  (evaluateM applySearch
    (prim (other div) (const 90)
      (prim plus (prim (other choose) (const (-5)) (const 5))
        (const 5)))).takeAll
```
```anchorInfo searchC
[9]
```
:::

## 独自の環境
%%%
tag := "custom-environments"
%%%

演算子として文字列を使えるようにし、文字列からそれを実装する関数への対応を用意すれば、評価器を利用者が拡張できるようにできる。
たとえば、利用者は評価器に剰余の演算子や、二つの引数の最大値を返す演算子を加えられる。
関数の名前から実装への対応を*環境*と呼ぶ。

環境は再帰呼び出しごとに渡す必要がある。
最初は、{anchorName evaluateM}`evaluateM`に環境を入れる引数がもう一つ必要で、その引数を再帰呼び出しのたびに渡さねばならないように思える。
しかし、このように引数を渡すのもモナドの一形態なので、適切な{anchorName evaluateM}`Monad`インスタンスがあれば評価器はそのまま使える。

関数をモナドとして使うことを通常*リーダーモナド*と呼ぶ。
リーダーモナドで式を評価するときには、次の規則を使う。
 * 定数$`n`は定数関数$`λ e . n`に評価される。
 * 算術演算子は引数をそのまま渡す関数に評価される。したがって$`f + g`は$`λ e . f(e) + g(e)`に評価される。
 * 独自の演算子は、その独自の演算子を引数に適用した結果に評価される。したがって$`f \ \mathrm{OP}\ g`は次のものに評価される。
   $$`
     λ e .
     \begin{cases}
     h(f(e), g(e)) & \mathrm{if}\ e\ \mathrm{contains}\ (\mathrm{OP}, h) \\
     0 & \mathrm{otherwise}
     \end{cases}
   `
   未知の演算子が適用された場合の代わりとして$`0`を使う。

:::paragraph
Leanでリーダーモナドを定義するには、まず{anchorName Reader}`Reader`型と、利用者が環境を手に入れられるようにする副作用を定義する。

```anchor Reader
def Reader (ρ : Type) (α : Type) : Type := ρ → α

def read : Reader ρ ρ := fun env => env
```
慣例により、環境にはギリシア文字{anchorName Reader}`ρ`（「ロー」と読む）を使う。
:::

:::paragraph
算術式の定数が定数関数に評価されることから、{anchorName Reader}`Reader`の{anchorName IdMonad}`pure`の適切な定義は定数関数であることが分かる。

```anchor ReaderPure
def Reader.pure (x : α) : Reader ρ α := fun _ => x
```
:::


一方、{anchorName MonadContract}`bind`はもう少しやっかいである。
その型は{anchorTerm readerBindType}`Reader ρ α → (α → Reader ρ β) → Reader ρ β`である。
{anchorName Reader}`Reader`の定義を展開すると{anchorTerm readerBindTypeEval}`(ρ → α) → (α → ρ → β) → (ρ → β)`になり、この型は分かりやすくなる。
一つ目の引数は環境を受け取る関数であり、二つ目の引数は、その環境を受け取る関数の結果をさらに別の環境を受け取る関数に変換するものであるべきである。
これらを組み合わせた結果もまた、環境を待つ関数である。

この関数を書く助けをLeanから対話的に得られる。
まず、できるだけ多くの助けを得るために引数と戻り値の型を明示的に書き、本体にはアンダースコアを置く。
```anchor readerbind0
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  _
```
Leanは、どの変数が使えるかと、結果に期待される型を説明するメッセージを出す。
{lit}`⊢`という記号は、地下鉄の改札に似ていることから{deftech}*ターンスタイル*と呼ばれ、ローカル変数と目標の型を区切る。このメッセージでは目標の型は{anchorTerm readerbind0}`ρ → β`である。
```anchorError readerbind0
don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
⊢ ρ → β
```

戻り値の型が関数なので、まずアンダースコアを{kw}`fun`で包むとよい。
```anchor readerbind1
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => _
```
するとメッセージには、関数の引数がローカル変数として現れる。
```anchorError readerbind1
don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ β
```

文脈の中で{anchorName readerbind2a}`β`を生み出せるのは{anchorName readerbind2a}`next`だけであり、そのためには引数が二つ要る。
それぞれの引数もまたアンダースコアにできる。
```anchor readerbind2a
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next _ _
```
二つのアンダースコアには、それぞれ次のメッセージが対応する。
```anchorError readerbind2a
don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ α
```
```anchorError readerbind2b
don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ ρ
```

:::paragraph
一つ目のアンダースコアに取りかかると、文脈の中で{anchorName readerbind3}`α`を生み出せるのは{anchorName readerbind3}`result`だけである。
```anchor readerbind3
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next (result _) _
```
これで両方のアンダースコアのエラーメッセージが同じになる。
```anchorError readerbind3
don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ ρ
```
:::

:::paragraph
幸い、両方のアンダースコアを{anchorName readerbind4}`env`に置き換えられる。

```anchor readerbind4
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next (result env) env
```
:::

{anchorName Readerbind}`Reader`の展開を戻し、明示的な細部を整理すれば最終的な版が得られる。

```anchor Readerbind
def Reader.bind
    (result : Reader ρ α)
    (next : α → Reader ρ β) : Reader ρ β :=
  fun env => next (result env) env
```

単に「型をたどる」だけで正しい関数を書けるとは限らず、できたプログラムを理解しないままになる危険もある。
しかし、まだ書かれていないプログラムより書かれたプログラムのほうが理解しやすいこともあり、アンダースコアを埋める過程から洞察が得られることもある。
この場合、{anchorName Readerbind}`Reader.bind`は{anchorName IdMonad}`Id`の{anchorName IdMonad}`bind`と同じように働くが、引数をもう一つ受け取ってそれを自分の引数に渡していく点が異なる。この直感が働きを理解する助けになる。

{anchorName ReaderPure}`Reader.pure`（定数関数を作る）と{anchorName Readerbind}`Reader.bind`はモナドの契約を満たす。
{anchorTerm ReaderMonad1}`Reader.bind (Reader.pure v) f`が{anchorTerm ReaderMonad1}`f v`と同じであることを確かめるには、最後の段階まで定義を置き換えていけばよい。
```anchorEvalSteps ReaderMonad1
Reader.bind (Reader.pure v) f
===>
fun env => f ((Reader.pure v) env) env
===>
fun env => f ((fun _ => v) env) env
===>
fun env => f v env
===>
f v
```
どの関数{anchorName eta}`f`についても{anchorTerm eta}`fun x => f x`は{anchorName eta}`f`と同じなので、契約の最初の部分は満たされる。
{anchorTerm ReaderMonad2}`Reader.bind r Reader.pure`が{anchorName ReaderMonad2}`r`と同じであることも、同じやり方で確かめられる。
```anchorEvalSteps ReaderMonad2
Reader.bind r Reader.pure
===>
fun env => Reader.pure (r env) env
===>
fun env => (fun _ => (r env)) env
===>
fun env => r env
```
リーダーの動作{anchorName ReaderMonad2}`r`自体が関数なので、これは{anchorName ReaderMonad2}`r`と同じである。
結合性を確かめるには、{anchorEvalStep ReaderMonad3a 0}`Reader.bind (Reader.bind r f) g`と{anchorEvalStep ReaderMonad3b 0}`Reader.bind r (fun x => Reader.bind (f x) g)`の両方について同じことをすればよい。
```anchorEvalSteps ReaderMonad3a
Reader.bind (Reader.bind r f) g
===>
fun env => g ((Reader.bind r f) env) env
===>
fun env => g ((fun env' => f (r env') env') env) env
===>
fun env => g (f (r env) env) env
```

{anchorEvalStep ReaderMonad3b 0}`Reader.bind r (fun x => Reader.bind (f x) g)`も同じ式に簡約される。
```anchorEvalSteps ReaderMonad3b
Reader.bind r (fun x => Reader.bind (f x) g)
===>
Reader.bind r (fun x => fun env => g (f x env) env)
===>
fun env => (fun x => fun env' => g (f x env') env') (r env) env
===>
fun env => (fun env' => g (f (r env) env') env') env
===>
fun env => g (f (r env) env) env
```

したがって{anchorTerm MonadReaderInst}`Monad (Reader ρ)`インスタンスが正当化される。

```anchor MonadReaderInst
instance : Monad (Reader ρ) where
  pure x := fun _ => x
  bind x f := fun env => f (x env) env
```

式の評価器に渡す独自の環境は、組のリストとして表せる。

```anchor Env
abbrev Env : Type := List (String × (Int → Int → Int))
```
たとえば{anchorName exampleEnv}`exampleEnv`には最大値と剰余の関数が入っている。

```anchor exampleEnv
def exampleEnv : Env := [("max", max), ("mod", (· % ·))]
```

Leanには、組のリストでキーに対応する値を探す{anchorName etc}`List.lookup`がすでにあるので、{anchorName applyPrimReader}`applyPrimReader`は独自の関数が環境にあるかどうかを調べるだけでよい。関数が未知なら{anchorTerm applyPrimReader}`0`を返す。

```anchor applyPrimReader
def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int :=
  read >>= fun env =>
  match env.lookup op with
  | none => pure 0
  | some f => pure (f x y)
```

{anchorName readerEval}`evaluateM`を{anchorName readerEval}`applyPrimReader`と式に組み合わせると、環境を期待する関数ができる。
幸い、{anchorName readerEval}`exampleEnv`がある。
```anchor readerEval
open Expr Prim in
#eval
  evaluateM applyPrimReader
    (prim (other "max") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv
```
```anchorInfo readerEval
9
```

{anchorName Many (module:=Examples.Monads.Many)}`Many`と同じく、{anchorName Reader}`Reader`はほとんどの言語では符号化しにくい副作用の例だが、型クラスとモナドのおかげで他のどの副作用と同じくらい便利に使える。
Common Lisp、Clojure、Emacs Lispにある動的変数や特別な変数は{anchorName Reader}`Reader`のように使える。
同様に、SchemeやRacketのパラメータオブジェクトは{anchorName Reader}`Reader`にちょうど対応する副作用である。
Kotlinのコンテキストオブジェクトという書き方でも似た問題を解けるが、それは根本的には関数の引数を自動で渡す手段なので、言語の副作用というよりリーダーモナドとしての符号化に近い。

## 練習問題
%%%
tag := "monads-arithmetic-example-exercises"
%%%

### 契約の確認
%%%
tag := none
%%%

{anchorTerm StateMonad}`State σ`と{anchorTerm MonadOptionExcept}`Except ε`についてモナドの契約を確認せよ。


### 失敗のあるリーダー
%%%
tag := none
%%%
リーダーモナドの例を手直しし、独自の演算子が定義されていないときに単にゼロを返すのではなく、失敗を示せるようにせよ。
言い換えれば、次の定義が与えられたとき、

```anchor ReaderFail
def ReaderOption (ρ : Type) (α : Type) : Type := ρ → Option α

def ReaderExcept (ε : Type) (ρ : Type) (α : Type) : Type := ρ → Except ε α
```
次のことを行え。
 1. 適切な{lit}`pure`と{lit}`bind`の関数を書く。
 2. これらの関数が{anchorName evaluateM}`Monad`の契約を満たすことを確認する。
 3. {anchorName ReaderFail}`ReaderOption`と{anchorName ReaderFail}`ReaderExcept`の{anchorName evaluateM}`Monad`インスタンスを書く。
 4. 適切な{anchorName evaluateM}`applyPrim`演算子を定義し、いくつかの例の式で{anchorName evaluateM}`evaluateM`と組み合わせて試す。

### 追跡する評価器
%%%
tag := "monads-arithmetic-example-exercise-trace"
%%%

{anchorName MonadWriter}`WithLog`型を評価器と組み合わせると、一部の操作の追跡を任意で加えられる。
特に{anchorName ToTrace}`ToTrace`型は、ある演算子を追跡する合図として使える。

```anchor ToTrace
inductive ToTrace (α : Type) : Type where
  | trace : α → ToTrace α
```
追跡する評価器では、式の型は{anchorTerm ToTraceExpr}`Expr (Prim (ToTrace (Prim Empty)))`とする。
これは、式の演算子が加算、減算、乗算と、それぞれを追跡する版から成ることを述べている。最も内側の引数が{anchorName ToTraceExpr}`Empty`であるのは、{anchorName ToTrace}`trace`の内側にはそれ以上の特別な演算子はなく、基本の三つだけであることを示すためである。

次のことを行え。
 1. {anchorTerm MonadWriter}`Monad (WithLog logged)`インスタンスを実装する。
 2. 追跡する演算子をその引数に適用し、演算子と引数の両方を記録する{anchorName applyTracedType}`applyTraced`関数を、型{anchorTerm applyTracedType}`ToTrace (Prim Empty) → Int → Int → WithLog (Prim Empty × Int × Int) Int`で書く。

この練習問題が正しくできていれば、
```anchor evalTraced
open Expr Prim ToTrace in
#eval
  evaluateM applyTraced
    (prim (other (trace times))
      (prim (other (trace plus)) (const 1)
        (const 2))
      (prim (other (trace minus)) (const 3)
        (const 4)))
```
次の結果になるはずである。
```anchorInfo evalTraced
{ log := [(Prim.plus, 1, 2), (Prim.minus, 3, 4), (Prim.times, 3, -1)], val := -3 }
```

 ヒント: 得られるログには型{anchorTerm ToTraceExpr}`Prim Empty`の値が現れる。{kw}`#eval`の結果として表示するには、次のインスタンスが要る。

```anchor ReprInstances
deriving instance Repr for WithLog
deriving instance Repr for Empty
deriving instance Repr for Prim
```
