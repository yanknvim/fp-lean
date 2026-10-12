module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads.Do"

#doc (Manual) "{kw}`do`-Notation for Monads" =>
%%%
tag := "monad-do-notation"
%%%

モナドに基づくAPIはとても強力だが、{lit}`>>=`を無名関数と組み合わせて明示的に使うのはまだ少し煩わしい。
{anchorName names}`HAdd.hAdd`を明示的に呼び出す代わりに中置演算子を使うのと同じように、Leanには*{kw}`do`記法*と呼ばれるモナドのための構文があり、モナドを使うプログラムを読み書きしやすくできる。
これは{anchorName names}`IO`でプログラムを書くのに使うのとまったく同じ{kw}`do`記法であり、{anchorName names}`IO`もモナドである。

{ref "hello-world"}[Hello, World!]では、{kw}`do`構文を使って{anchorName names}`IO`の動作を組み合わせたが、それらのプログラムの意味は直接説明した。
モナドを使ったプログラミングを理解した今は、{kw}`do`がその下にあるモナドの演算子の使用へとどのように変換されるかという形で説明できる。

{kw}`do`の最初の変換は、{kw}`do`の中の文が単一の式{anchorName doSugar1a}`E`だけのときに使う。
この場合、{kw}`do`は取り除かれ、次のようになる。
```anchor doSugar1a
do E
```
次のように変換される。
```anchor doSugar1b
E
```

二つ目の変換は、{kw}`do`の最初の文が矢印付きの{kw}`let`でローカル変数を束縛するときに使う。
これは{lit}`>>=`と、まさにその変数を束縛する関数を組み合わせた形に変換される。したがって、
```anchor doSugar2a
 do let x ← E₁
    Stmt
    …
    Eₙ
```
次のように変換される。
```anchor doSugar2b
E₁ >>= fun x =>
  do Stmt
     …
     Eₙ
```

{kw}`do`ブロックの最初の文が式なら、それは{anchorName names}`Unit`を返すモナドの動作と見なされるので、関数は{anchorName names}`Unit`のコンストラクタにマッチする。したがって、
```anchor doSugar3a
  do E₁
     Stmt
     …
     Eₙ
```
次のように変換される。
```anchor doSugar3b
E₁ >>= fun () =>
  do Stmt
     …
     Eₙ
```

最後に、{kw}`do`ブロックの最初の文が{lit}`:=`を使う{kw}`let`なら、変換した形は普通のlet式である。したがって、
```anchor doSugar4a
do let x := E₁
   Stmt
   …
   Eₙ
```
次のように変換される。
```anchor doSugar4b
let x := E₁
do Stmt
   …
   Eₙ
```

:::paragraph
{anchorName firstThirdFifthSeventhMonad (module := Examples.Monads.Class)}`Monad`クラスを使う{anchorName firstThirdFifthSeventhMonad (module := Examples.Monads.Class)}`firstThirdFifthSeventh`の定義は次のとおりである。

```anchor firstThirdFifthSeventhMonad (module := Examples.Monads.Class)
def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α)
    (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)
```
{kw}`do`記法を使うと、ずっと読みやすくなる。
```anchor firstThirdFifthSeventhDo
def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α)
    (xs : List α) : m (α × α × α × α) := do
  let first ← lookup xs 0
  let third ← lookup xs 2
  let fifth ← lookup xs 4
  let seventh ← lookup xs 6
  pure (first, third, fifth, seventh)
```
:::

:::paragraph
{anchorName mapM}`Monad`型クラスを使わない場合、木の節点に番号を振る{anchorName numberMonadicish (module := Examples.Monads)}`number`関数は次のように書いていた。

```anchor numberMonadicish (module := Examples.Monads)
def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => ok BinTree.leaf
    | BinTree.branch left x right =>
      helper left ~~> fun numberedLeft =>
      get ~~> fun n =>
      set (n + 1) ~~> fun () =>
      helper right ~~> fun numberedRight =>
      ok (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd
```
{anchorName mapM}`Monad`と{kw}`do`を使うと、その定義はずっと煩わしくない。

```anchor numberDo
def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => pure BinTree.leaf
    | BinTree.branch left x right => do
      let numberedLeft ← helper left
      let n ← get
      set (n + 1)
      let numberedRight ← helper right
      ok (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd
```
:::

{anchorName names}`IO`で{kw}`do`を使うときの便利さは、他のモナドで使うときにもすべて得られる。
たとえば、入れ子にした動作もどのモナドでも働く。
{anchorName mapM (module:=Examples.Monads.Class)}`mapM`の元の定義は次のとおりだった。

```anchor mapM (module := Examples.Monads.Class)
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM f xs >>= fun tl =>
    pure (hd :: tl)
```
{kw}`do`記法を使うと次のように書ける。

```anchor mapM
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    let hd ← f x
    let tl ← mapM f xs
    pure (hd :: tl)
```
入れ子にした動作を使うと、元のモナドでない{anchorName names}`map`とほとんど同じ長さになる。

```anchor mapMNested
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    pure ((← f x) :: (← mapM f xs))
```
入れ子にした動作を使うと、{anchorName numberDoShort}`number`をずっと簡潔にできる。

```anchor numberDoShort
def increment : State Nat Nat := do
  let n ← get
  set (n + 1)
  pure n

def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => pure BinTree.leaf
    | BinTree.branch left x right => do
      pure
        (BinTree.branch
          (← helper left)
          ((← increment), x)
          (← helper right))
  (helper t 0).snd
```



# 練習問題
%%%
tag := "monad-do-notation-exercises"
%%%

 * {anchorName evaluateM (module:=Examples.Monads.Class)}`evaluateM`とその補助関数、および個々の利用例を、{lit}`>>=`の明示的な呼び出しの代わりに{kw}`do`記法を使って書き直せ。
 * {anchorName firstThirdFifthSeventhDo}`firstThirdFifthSeventh`を入れ子にした動作を使って書き直せ。
