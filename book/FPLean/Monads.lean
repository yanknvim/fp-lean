module
public import VersoManual
import FPLean.Examples

import FPLean.Monads.Class
import FPLean.Monads.Arithmetic
import FPLean.Monads.Do
import FPLean.Monads.IO
import FPLean.Monads.Conveniences
import FPLean.Monads.Summary


open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads"

#doc (Manual) "Monads" =>
%%%
tag := "monads"
%%%

C#とKotlinでは、{CSharp}`?.`演算子は、nullかもしれない値のプロパティを参照したりメソッドを呼び出したりする手段である。
レシーバが{CSharp}`null`なら、式全体がnullになる。
そうでなければ、その下にある非{CSharp}`null`の値が呼び出しを受け取る。
{CSharp}`?.`は連鎖させられ、その場合、最初の{Kotlin}`null`の結果で参照の連鎖が終わる。
このようにnullチェックを連鎖させるのは、深く入れ子になった{kw}`if`を書いて保守するよりずっと便利である。

同様に、例外は、エラーコードを手で調べて伝播させるよりずっと便利である。
同時に、ログは、各関数がログの結果と戻り値の両方を返すのではなく、ログ専用のフレームワークを用意するのが最も簡単である。
連鎖するnullチェックと例外は通常、言語の設計者がこの用途をあらかじめ想定している必要があるが、ログのフレームワークは通常、副作用を利用して、ログを出すコードとログの蓄積を切り離す。

# 一つのAPI、多くの用途
%%%
tag := "monad-api-examples"
%%%

これらの機能もそれ以外もすべて、{moduleName}`Monad`という共通のAPIのインスタンスとして、ライブラリのコードで実装できる。
LeanにはこのAPIを使いやすくする専用の記法があり、それが裏で何が起きているかの理解を妨げることもある。
この章は、nullチェックを手で入れ子にする泥臭い説明から始め、そこから便利で一般的なAPIへと進む。
その間は、多少強引でも話を信じて読み進めてほしい。

## {lit}`none`のチェック: 繰り返しを避ける
%%%
tag := "example-option-monad"
%%%

:::paragraph
Leanでは、パターンマッチングでnullのチェックを連鎖させられる。
リストの最初の要素を取り出すには、オプションの参照記法を使えばよい。

```anchor first
def first (xs : List α) : Option α :=
  xs[0]?
```
:::

:::paragraph
空のリストには最初の要素がないので、結果は{anchorName first}`Option`でなければならない。
最初と三番目の要素を取り出すには、それぞれが{moduleName}`none`でないことを調べる必要がある。

```anchor firstThird
def firstThird (xs : List α) : Option (α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      some (first, third)
```
同様に、最初と三番目と五番目の要素を取り出すには、値が{moduleName}`none`でないことをさらに調べる必要がある。

```anchor firstThirdFifth
def firstThirdFifth (xs : List α) : Option (α × α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      match xs[4]? with
      | none => none
      | some fifth =>
        some (first, third, fifth)
```
そしてこの列に七番目の要素を加えると、かなり手に負えなくなってくる。

```anchor firstThirdFifthSeventh
def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      match xs[4]? with
      | none => none
      | some fifth =>
        match xs[6]? with
        | none => none
        | some seventh =>
          some (first, third, fifth, seventh)
```
:::

:::paragraph
このコードの根本的な問題は、二つの関心事を同時に扱っていることである。要素を取り出すことと、それらがすべて存在することを調べることだ。
二つ目の関心事は、{moduleName}`none`の場合を扱うコードをコピーして貼り付けることで処理している。
繰り返し現れる部分を補助関数に切り出すのは、よくあるよい書き方である。

```anchor andThenOption
def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some x => next x
```
この補助関数は、C#やKotlinの{CSharp}`?.`と同じように使うもので、{moduleName}`none`の値の伝播を引き受ける。
引数を二つ取る。オプションの値と、その値が{moduleName}`none`でないときに適用する関数である。
一つ目の引数が{moduleName}`none`なら、補助関数は{moduleName}`none`を返す。
一つ目の引数が{moduleName}`none`でなければ、{moduleName}`some`コンストラクタの中身に関数が適用される。
:::

:::paragraph
そこで{anchorName firstThirdandThen}`firstThird`は、パターンマッチングの代わりに{anchorName firstThirdandThen}`andThen`を使う形に書き換えられる。

```anchor firstThirdandThen
def firstThird (xs : List α) : Option (α × α) :=
  andThen xs[0]? fun first =>
  andThen xs[2]? fun third =>
  some (first, third)
```
Leanでは、関数を引数として渡すときに括弧で囲む必要はない。
次の同等な定義は、括弧を多く使い、関数の本体を字下げしている。

```anchor firstThirdandThenExpl
def firstThird (xs : List α) : Option (α × α) :=
  andThen xs[0]? (fun first =>
    andThen xs[2]? (fun third =>
      some (first, third)))
```
{anchorName firstThirdandThenExpl}`andThen`補助関数は、値が流れる一種の「パイプライン」を提供しており、やや変わった字下げの版のほうがこのことをよく表している。
{anchorName firstThirdandThenExpl}`andThen`を書くための構文をよくすれば、これらの計算はさらに理解しやすくなる。
:::

### 中置演算子
%%%
tag := "defining-infix-operators"
%%%


Leanでは、{kw}`infix`、{kw}`infixl`、{kw}`infixr`のコマンドで中置演算子を宣言できる。それぞれ非結合、左結合、右結合の演算子を作る。
{deftech}*左結合*の演算子を続けて複数回使うと、開き括弧が式の左側に積み重なる。
加算演算子{lit}`+`は左結合なので、{anchorTerm plusFixity}`w + x + y + z`は{anchorTerm plusFixity}`(((w + x) + y) + z)`と等しい。
累乗演算子{lit}`^`は右結合なので、{anchorTerm powFixity}`w ^ x ^ y ^ z`は{anchorTerm powFixity}`w ^ (x ^ (y ^ z))`と等しい。
{lit}`<`のような比較演算子は非結合なので、{lit}`x < y < z`は構文エラーになり、手で括弧を付ける必要がある。

:::paragraph
次の宣言は{anchorName andThenOptArr}`andThen`を中置演算子にする。

```anchor andThenOptArr
infixl:55 " ~~> " => andThen
```
コロンの後に続く数が、新しい中置演算子の{deftech}*優先度*を宣言する。
普通の数学の記法では、{lit}`+`も{lit}`*`も左結合であるにもかかわらず、{anchorTerm plusTimesPrec}`x + y * z`は{anchorTerm plusTimesPrec}`x + (y * z)`と等しい。
Leanでは{lit}`+`の優先度は65、{lit}`*`の優先度は70である。
優先度の高い演算子が、優先度の低い演算子より先に適用される。
{lit}`~~>`の宣言によれば、{lit}`+`も{lit}`*`も優先度が高いので、先に適用される。
ふつう、ある一群の演算子にとって最も便利な優先度を決めるには、試行錯誤と多数の例が必要である。
:::

新しい中置演算子の後には二重矢印{lit}`=>`があり、その中置演算子に使う名前付きの関数を指定する。
Leanの標準ライブラリはこの機能を使い、{lit}`+`と{lit}`*`をそれぞれ{moduleName}`HAdd.hAdd`と{moduleName}`HMul.hMul`を指す中置演算子として定義し、型クラスで中置演算子をオーバーロードできるようにしている。
しかしここでは、{anchorName firstThirdandThen}`andThen`はただの普通の関数である。

:::paragraph
{anchorName andThenOptArr}`andThen`の中置演算子を定義したので、{anchorName firstThirdInfix (show := firstThird)}`firstThirdInfix`は、{moduleName}`none`のチェックの「パイプライン」らしさが前面に出る形に書き換えられる。

```anchor firstThirdInfix
def firstThirdInfix (xs : List α) : Option (α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  some (first, third)
```
この書き方は、大きな関数を書くときにはるかに簡潔である。
```anchor firstThirdFifthSeventInfix
def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  xs[4]? ~~> fun fifth =>
  xs[6]? ~~> fun seventh =>
  some (first, third, fifth, seventh)
```
:::

## エラーメッセージの伝播
%%%
tag := "example-except-monad"
%%%

Leanのような純粋な関数型言語には、エラー処理のための例外の仕組みが組み込まれていない。例外を投げたり捕まえたりするのは、式を一段ずつ評価するモデルの外にあるためである。
しかし、関数型のプログラムにもエラー処理は当然必要である。
{anchorName firstThirdFifthSeventInfix}`firstThirdFifthSeventh`の場合、リストがどれだけの長さで、どこで参照に失敗したかを利用者が知れるのは役に立つはずである。

:::paragraph
これは通常、エラーか結果のどちらかになるデータ型を定義し、例外を使う関数をそのデータ型を返す関数に置き換えることで実現する。

```anchor Except
inductive Except (ε : Type) (α : Type) where
  | error : ε → Except ε α
  | ok : α → Except ε α
deriving BEq, Hashable, Repr
```
型変数{anchorName Except}`ε`は、その関数が生み出しうるエラーの型を表す。
呼び出し側はエラーと成功の両方を扱うことが期待され、そのため型変数{anchorName Except}`ε`はJavaの検査例外の一覧に少し似た役割を果たす。
:::

:::paragraph
{anchorName first}`Option`と同様に、{anchorName Except}`Except`はリストの要素が見つからなかったことを示すのに使える。
この場合、エラーの型は{moduleName}`String`である。

```anchor getExcept
def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => Except.ok x
```
範囲内の値を参照すると{anchorName ExceptExtra}`Except.ok`になる。
```anchor ediblePlants
def ediblePlants : List String :=
  ["ramsons", "sea plantain", "sea buckthorn", "garden nasturtium"]
```
```anchor success
#eval get ediblePlants 2
```
```anchorInfo success
Except.ok "sea buckthorn"
```
範囲外の値を参照すると{anchorName ExceptExtra}`Except.error`になる。
```anchor failure
#eval get ediblePlants 4
```
```anchorInfo failure
Except.error "Index 4 not found (maximum is 3)"
```
:::

:::paragraph
リストの参照が一回だけなら、値かエラーを返せばよく、便利である。
```anchor firstExcept
def first (xs : List α) : Except String α :=
  get xs 0
```
しかし、リストの参照を二回行うと、起こりうる失敗を扱う必要がある。
```anchor firstThirdExcept
def firstThird (xs : List α) : Except String (α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      Except.ok (first, third)
```
この関数にリストの参照をもう一つ加えると、さらに多くのエラー処理が必要になる。
```anchor firstThirdFifthExcept
def firstThirdFifth (xs : List α) : Except String (α × α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      match get xs 4 with
      | Except.error msg => Except.error msg
      | Except.ok fifth =>
        Except.ok (first, third, fifth)
```
そしてリストの参照をもう一つ加えると、かなり手に負えなくなってくる。
```anchor firstThirdFifthSeventhExcept
def firstThirdFifthSeventh (xs : List α) : Except String (α × α × α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      match get xs 4 with
      | Except.error msg => Except.error msg
      | Except.ok fifth =>
        match get xs 6 with
        | Except.error msg => Except.error msg
        | Except.ok seventh =>
          Except.ok (first, third, fifth, seventh)
```
:::

:::paragraph
ここでもまた、共通のパターンを補助関数としてくくり出せる。
この関数の各段階ではエラーを調べ、結果が成功だったときにだけ残りの計算に進む。
{anchorName andThenExcept}`Except`用に{anchorName andThenExcept}`andThen`の新しい版を定義できる。

```anchor andThenExcept
def andThen (attempt : Except e α) (next : α → Except e β) : Except e β :=
  match attempt with
  | Except.error msg => Except.error msg
  | Except.ok x => next x
```
{anchorName first}`Option`のときと同じように、この版の{anchorName andThenExcept}`andThen`を使えば{anchorName firstThirdAndThenExcept}`firstThird'`をより簡潔に定義できる。

```anchor firstThirdAndThenExcept
def firstThird' (xs : List α) : Except String (α × α) :=
  andThen (get xs 0) fun first  =>
  andThen (get xs 2) fun third =>
  Except.ok (first, third)
```
:::

:::paragraph
{anchorName first}`Option`の場合も{anchorName andThenExcept}`Except`の場合も、繰り返し現れるパターンが二つある。各段階で中間結果を調べる部分は{anchorName andThenExcept}`andThen`にくくり出し、最後の成功の結果はそれぞれ{moduleName}`some`と{anchorName andThenExcept}`Except.ok`である。
便宜上、成功のほうも{anchorName okExcept}`ok`という補助関数にくくり出せる。

```anchor okExcept
def ok (x : α) : Except ε α := Except.ok x
```
同様に、失敗のほうも{anchorName failExcept}`fail`という補助関数にくくり出せる。

```anchor failExcept
def fail (err : ε) : Except ε α := Except.error err
```
{anchorName okExcept}`ok`と{anchorName failExcept}`fail`を使うと、{anchorName getExceptEffects}`get`が少し読みやすくなる。

```anchor getExceptEffects
def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => fail s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => ok x
```
:::

:::paragraph
{anchorName andThenExceptInfix}`andThen`の中置宣言を加えれば、{anchorName firstThirdInfixExcept}`firstThird`は{anchorName first}`Option`を返す版と同じくらい簡潔になる。

```anchor andThenExceptInfix
infixl:55 " ~~> " => andThen
```

```anchor firstThirdInfixExcept
def firstThird (xs : List α) : Except String (α × α) :=
  get xs 0 ~~> fun first =>
  get xs 2 ~~> fun third =>
  ok (first, third)
```
このやり方は、大きな関数にも同じように当てはまる。

```anchor firstThirdFifthSeventInfixExcept
def firstThirdFifthSeventh (xs : List α) : Except String (α × α × α × α) :=
  get xs 0 ~~> fun first =>
  get xs 2 ~~> fun third =>
  get xs 4 ~~> fun fifth =>
  get xs 6 ~~> fun seventh =>
  ok (first, third, fifth, seventh)
```

:::

## ログ
%%%
tag := "logging"
%%%

:::paragraph
数を2で割って余りが出ないとき、その数は偶数である。
```anchor isEven
def isEven (i : Int) : Bool :=
  i % 2 == 0
```
{anchorName sumAndFindEvensDirect}`sumAndFindEvens`関数は、リストの和を計算しつつ、途中で出会った偶数を覚えておく。
```anchor sumAndFindEvensDirect
def sumAndFindEvens : List Int → List Int × Int
  | [] => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens is
    (if isEven i then i :: moreEven else moreEven, sum + i)
```
:::

:::paragraph
この関数は、よくあるパターンを単純化した例である。
多くのプログラムは、データ構造を一度だけたどりながら、主たる結果を計算すると同時に、副次的な追加の結果を蓄積する必要がある。
その一例がログである。{moduleName}`IO`の動作であるプログラムはいつでもディスク上のファイルにログを書けるが、ディスクはLeanの関数の数学的な世界の外にあるので、{moduleName}`IO`に基づいてログについて何かを証明するのはずっと難しくなる。
もう一つの例は、木のすべての節点の和を中間順のたどり方で計算しつつ、訪れた節点を同時に記録する関数である。

```anchor inorderSum
def inorderSum : BinTree Int → List Int × Int
  | BinTree.leaf => ([], 0)
  | BinTree.branch l x r =>
    let (leftVisited, leftSum) := inorderSum l
    let (hereVisited, hereSum) := ([x], x)
    let (rightVisited, rightSum) := inorderSum r
    (leftVisited ++ hereVisited ++ rightVisited,
     leftSum + hereSum + rightSum)
```
:::

{anchorName sumAndFindEvensDirect}`sumAndFindEvens`も{anchorName inorderSum}`inorderSum`も、共通する繰り返しの構造を持つ。
計算の各段階は、保存しておくデータのリストと、主たる結果を組にして返す。
そしてリストを連結し、主たる結果を計算して連結したリストと組にする。
{anchorName sumAndFindEvensDirectish}`sumAndFindEvens`を少し書き換えて、偶数の保存と和の計算という関心事をよりきれいに分けると、共通の構造がはっきりしてくる。

```anchor sumAndFindEvensDirectish
def sumAndFindEvens : List Int → List Int × Int
  | [] => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens is
    let (evenHere, ()) := (if isEven i then [i] else [], ())
    (evenHere ++ moreEven, sum + i)
```

分かりやすさのために、蓄積した結果と値の組に独自の名前を付けられる。

```anchor WithLog
structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α
```
同様に、蓄積した結果のリストを保存しつつ、値を計算の次の段階に渡す処理も、ここでも{anchorName andThenWithLog}`andThen`という名前の補助関数にくくり出せる。

```anchor andThenWithLog
def andThen (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
  let {log := thisOut, val := thisRes} := result
  let {log := nextOut, val := nextRes} := next thisRes
  {log := thisOut ++ nextOut, val := nextRes}
```
エラーの場合、{anchorName okWithLog}`ok`は常に成功する操作を表していた。
しかしここでは、何も記録せずに値を返すだけの操作である。

```anchor okWithLog
def ok (x : β) : WithLog α β := {log := [], val := x}
```
{anchorName Except}`Except`が{anchorName failExcept}`fail`という可能性を用意しているのと同じように、{anchorName WithLog}`WithLog`でも項目をログに追加できるべきである。
これには取り立てて意味のある戻り値がないので、{anchorName save}`Unit`を返す。

```anchor save
def save (data : α) : WithLog α Unit :=
  {log := [data], val := ()}
```

{anchorName WithLog}`WithLog`、{anchorName andThenWithLog}`andThen`、{anchorName okWithLog}`ok`、{anchorName save}`save`を使うと、どちらのプログラムでもログの関心事を和の計算の関心事から分離できる。

```anchor sumAndFindEvensAndThen
def sumAndFindEvens : List Int → WithLog Int Int
  | [] => ok 0
  | i :: is =>
    andThen (if isEven i then save i else ok ()) fun () =>
    andThen (sumAndFindEvens is) fun sum =>
    ok (i + sum)
```

```anchor inorderSumAndThen
def inorderSum : BinTree Int → WithLog Int Int
  | BinTree.leaf => ok 0
  | BinTree.branch l x r =>
    andThen (inorderSum l) fun leftSum =>
    andThen (save x) fun () =>
    andThen (inorderSum r) fun rightSum =>
    ok (leftSum + x + rightSum)
```
そしてここでもまた、中置演算子が正しい段取りに目を向けやすくする。

```anchor infixAndThenLog
infixl:55 " ~~> " => andThen
```

```anchor withInfixLogging
def sumAndFindEvens : List Int → WithLog Int Int
  | [] => ok 0
  | i :: is =>
    (if isEven i then save i else ok ()) ~~> fun () =>
    sumAndFindEvens is ~~> fun sum =>
    ok (i + sum)

def inorderSum : BinTree Int → WithLog Int Int
  | BinTree.leaf => ok 0
  | BinTree.branch l x r =>
    inorderSum l ~~> fun leftSum =>
    save x ~~> fun () =>
    inorderSum r ~~> fun rightSum =>
    ok (leftSum + x + rightSum)
```

## 木の節点への番号付け
%%%
tag := "numbering-tree-nodes"
%%%

木の{deftech}*中間順の番号付け*とは、木の各データに、その木を中間順でたどったときに訪れる順番を対応させることである。
たとえば{anchorName aTree}`aTree`を考える。

```anchor aTree
open BinTree in
def aTree :=
  branch
    (branch
       (branch leaf "a" (branch leaf "b" leaf))
       "c"
       leaf)
    "d"
    (branch leaf "e" leaf)
```
その中間順の番号付けは次のようになる。
```anchorInfo numberATree
BinTree.branch
  (BinTree.branch
    (BinTree.branch (BinTree.leaf) (0, "a") (BinTree.branch (BinTree.leaf) (1, "b") (BinTree.leaf)))
    (2, "c")
    (BinTree.leaf))
  (3, "d")
  (BinTree.branch (BinTree.leaf) (4, "e") (BinTree.leaf))
```

:::paragraph
木は再帰関数で処理するのが最も自然だが、木に対する普通の再帰の形では中間順の番号付けを計算しにくい。
左部分木のどこかで割り当てられた最大の数が、その節点のデータの番号を決めるのに使われ、さらに右部分木の番号付けの開始点を決めるのにも使われるためである。
命令型言語では、次に割り当てる番号を入れた可変変数を使えばこの問題を避けられる。
次のPythonのプログラムは、可変変数を使って中間順の番号付けを計算する。
```includePython "../examples/inorder_python/inordernumbering.py" (anchor := code)
class Branch:
    def __init__(self, value, left=None, right=None):
        self.left = left
        self.value = value
        self.right = right
    def __repr__(self):
        return f'Branch({self.value!r}, left={self.left!r}, right={self.right!r})'

def number(tree):
    num = 0
    def helper(t):
        nonlocal num
        if t is None:
            return None
        else:
            new_left = helper(t.left)
            new_value = (num, t.value)
            num += 1
            new_right = helper(t.right)
            return Branch(left=new_left, value=new_value, right=new_right)

    return helper(tree)
```
{anchorName aTree}`aTree`に相当するPythonの木は次のとおりである。
```includePython "../examples/inorder_python/inordernumbering.py" (anchor := a_tree)
a_tree = Branch("d",
                left=Branch("c",
                            left=Branch("a", left=None, right=Branch("b")),
                            right=None),
                right=Branch("e"))
```
その番号付けは次のようになる。
```command inorderpy "inorder_python" (prompt := ">>> ") (show := "number(a_tree)")
python3 inordernumbering.py
```
```commandOut inorderpy "python3 inordernumbering.py"
Branch((3, 'd'), left=Branch((2, 'c'), left=Branch((0, 'a'), left=None, right=Branch((1, 'b'), left=None, right=None)), right=None), right=Branch((4, 'e'), left=None, right=None))
```
:::


Leanには可変変数がないが、回避策はある。
外から見れば、可変変数には関わりのある側面が二つあると考えられる。関数を呼び出したときの値と、関数が戻るときの値である。
言い換えれば、可変変数を使う関数は、その可変変数の初期値を引数に取り、変数の最終値と関数の結果の組を返す関数と見なせる。
この最終値は、次の段階に引数として渡せる。

:::paragraph
Pythonの例が、可変変数を用意する外側の関数と、その変数を変更する内側の補助関数を使っているのと同じように、Lean版の関数では、変数の初期値を与えて関数の結果を明示的に返す外側の関数と、変数の値を受け渡しながら番号を振った木を計算する内側の補助関数を使う。

```anchor numberDirect
def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper (n : Nat) : BinTree α → (Nat × BinTree (Nat × α))
    | BinTree.leaf => (n, BinTree.leaf)
    | BinTree.branch left x right =>
      let (k, numberedLeft) := helper n left
      let (i, numberedRight) := helper (k + 1) right
      (i, BinTree.branch numberedLeft (k, x) numberedRight)
  (helper 0 t).snd
```
このコードは、{moduleName}`none`を伝播させる{anchorName first}`Option`のコード、{anchorName exceptNames (show := error)}`Except.error`を伝播させる{anchorName exceptNames}`Except`のコード、ログを蓄積する{moduleName}`WithLog`のコードと同じく、二つの関心事を混ぜ合わせている。カウンタの値を伝播させることと、実際に木をたどって結果を求めることである。
それらの場合と同じく、計算のある段階から次の段階へ状態を伝播させる{anchorName andThenState}`andThen`補助関数を定義できる。
まず、入力の状態を引数に取り、出力の状態と値を組にして返すパターンに名前を付ける。

```anchor State
def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)
```
:::

:::paragraph
{anchorName State}`State`の場合、{anchorName okState}`ok`は、入力の状態を変えずに、与えられた値と一緒に返す関数である。
```anchor okState
def ok (x : α) : State σ α :=
  fun s => (s, x)
```
:::

:::paragraph
可変変数を扱うときには、基本的な操作が二つある。値を読み出すことと、新しい値に置き換えることである。
現在の値を読み出すには、入力の状態をそのまま出力の状態に入れ、同時に値のフィールドにも入れる関数を使う。
```anchor get
def get : State σ σ :=
  fun s => (s, s)
```
新しい値を書き込むには、入力の状態を無視し、与えられた新しい値を出力の状態に入れる。
```anchor set
def set (s : σ) : State σ Unit :=
  fun _ => (s, ())
```
:::

:::paragraph
最後に、状態を使う二つの計算は、一つ目の関数の出力の状態と戻り値の両方を求め、それらを両方とも次の関数に渡すことで順につなげられる。

```anchor andThenState
def andThen (first : State σ α) (next : α → State σ β) : State σ β :=
  fun s =>
    let (s', x) := first s
    next x s'

infixl:55 " ~~> " => andThen
```
:::

:::paragraph
{anchorName State}`State`とその補助関数を使えば、局所的な可変状態をまねられる。

```anchor numberMonadicish
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
{anchorName State}`State`は一つの局所変数しかまねないので、{anchorName get}`get`と{anchorName set}`set`は特定の変数名を指す必要がない。
:::

## モナド: 関数型の設計パターン
%%%
tag := "monad-as-design-pattern"
%%%

これらの例はいずれも、次のものから成っていた。
 * {anchorName first}`Option`、{anchorTerm okExcept}`Except ε`、{anchorTerm save}`WithLog α`、{anchorTerm andThenState}`State σ`のような多相型
 * この型を持つプログラムをつなげる際の繰り返しの部分を引き受ける{lit}`andThen`演算子
 * その型を使う最も退屈な方法（の一種）である{lit}`ok`演算子
 * {moduleName}`none`、{anchorName failExcept}`fail`、{anchorName save}`save`、{anchorName get}`get`など、その型の使い方に名前を付けたその他の操作

この形のAPIを{deftech}*モナド*と呼ぶ。
モナドの考え方は圏論と呼ばれる数学の分野に由来するが、プログラミングに使うのに圏論の理解は要らない。
モナドの要点は、純粋な関数型言語であるLeanの備える道具を使って、それぞれのモナドが特定の種類の副作用を符号化することである。
たとえば{anchorName first}`Option`は{moduleName}`none`を返して失敗しうるプログラムを表し、{moduleName}`Except`は例外を投げうるプログラムを、{moduleName}`WithLog`は実行中にログを蓄積するプログラムを、{anchorName State}`State`は一つの可変変数を持つプログラムを表す。

{include 1 FPLean.Monads.Class}

{include 1 FPLean.Monads.Arithmetic}

{include 1 FPLean.Monads.Do}

{include 1 FPLean.Monads.IO}

{include 1 FPLean.Monads.Conveniences}

{include 1 FPLean.Monads.Summary}
