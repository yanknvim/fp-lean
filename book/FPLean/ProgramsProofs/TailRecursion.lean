module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.TCO"

#doc (Manual) "Tail Recursion" =>
%%%
tag := "tail-recursion"
%%%

Leanの{kw}`do`記法を使えば{kw}`for`や{kw}`while`のような伝統的なループの構文を使えるが、これらの構成は裏で再帰関数の呼び出しに変換される。
ほとんどのプログラミング言語で、再帰関数はループに対して重大な欠点がある。ループはスタックの空間を消費しないが、再帰関数は再帰呼び出しの回数に比例するスタックの空間を消費する。
スタックの空間は通常限られており、自然に再帰関数として表される算法を、明示的な可変のヒープ上のスタックを伴うループとして書き直す必要がしばしばある。

関数型プログラミングでは、通常は逆である。
自然に可変のループとして表されるプログラムがスタックの空間を消費することがあり、再帰関数に書き直すと速く動くことがある。
これは関数型プログラミング言語の重要な側面による。*末尾呼び出しの除去*である。
末尾呼び出しとは、ある関数から別の関数への呼び出しで、新しいスタックフレームを積むのではなく現在のスタックフレームを置き換える通常のジャンプにコンパイルできるものであり、末尾呼び出しの除去とはこの変換を実装する処理である。

末尾呼び出しの除去は、単に任意の最適化というわけではない。
それが備わっていることは、効率のよい関数型のコードを書けるようにするための根本的な部分である。
役に立つには、信頼できるものでなければならない。
プログラマは末尾呼び出しを確実に見分けられねばならず、コンパイラがそれを除去することを信頼できねばならない。

{anchorName NonTailSum}`NonTail.sum`関数は{anchorName NonTailSum}`Nat`のリストの中身を足す。

```anchor NonTailSum
def NonTail.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs
```
この関数をリスト{anchorTerm NonTailSumOneTwoThree}`[1, 2, 3]`に適用すると、次の評価の段階の並びになる。
```anchorEvalSteps NonTailSumOneTwoThree
NonTail.sum [1, 2, 3]
===>
1 + (NonTail.sum [2, 3])
===>
1 + (2 + (NonTail.sum [3]))
===>
1 + (2 + (3 + (NonTail.sum [])))
===>
1 + (2 + (3 + 0))
===>
1 + (2 + 3)
===>
1 + 5
===>
6
```
評価の段階で、括弧は{anchorName NonTailSumOneTwoThree}`NonTail.sum`への再帰呼び出しを表す。
言い換えれば、三つの数を足すには、プログラムはまずリストが空でないことを調べねばならない。
リストの先頭（{anchorTerm NonTailSumOneTwoThree}`1`）をリストの残りの和に足すには、まずリストの残りの和を計算する必要がある。
```anchorEvalStep NonTailSumOneTwoThree 1
1 + (NonTail.sum [2, 3])
```
しかしリストの残りの和を計算するには、プログラムはそれが空かどうかを調べねばならない。
空ではない。残り自体が{anchorTerm NonTailSumOneTwoThree}`2`を先頭に持つリストである。
その結果の段階は{anchorTerm NonTailSumOneTwoThree}`NonTail.sum [3]`の返りを待っている。
```anchorEvalStep NonTailSumOneTwoThree 2
1 + (2 + (NonTail.sum [3]))
```
実行時の呼び出しスタックの狙いは、値{anchorTerm NonTailSumOneTwoThree}`1`、{anchorTerm NonTailSumOneTwoThree}`2`、{anchorTerm NonTailSumOneTwoThree}`3`と、それらを再帰呼び出しの結果に足すという指示を覚えておくことにある。
再帰呼び出しが完了するにつれ、制御はその呼び出しを行ったスタックフレームに戻り、各段階の足し算が行われる。
リストの先頭とそれらを足す指示を保持するのには費用がかかる。リストの長さに比例する空間を要するのである。

{anchorName TailSum}`Tail.sum`関数も{anchorName TailSum}`Nat`のリストの中身を足す。

```anchor TailSum
def Tail.sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs

def Tail.sum (xs : List Nat) : Nat :=
  Tail.sumHelper 0 xs
```
これをリスト{anchorTerm TailSumOneTwoThree}`[1, 2, 3]`に適用すると、次の評価の段階の並びになる。
```anchorEvalSteps TailSumOneTwoThree
Tail.sum [1, 2, 3]
===>
Tail.sumHelper 0 [1, 2, 3]
===>
Tail.sumHelper (0 + 1) [2, 3]
===>
Tail.sumHelper 1 [2, 3]
===>
Tail.sumHelper (1 + 2) [3]
===>
Tail.sumHelper 3 [3]
===>
Tail.sumHelper (3 + 3) []
===>
Tail.sumHelper 6 []
===>
6
```
内側の補助関数は再帰的に自分自身を呼び出すが、最終的な結果を計算するのに何も覚えておく必要がないように呼び出す。
{anchorName TailSum}`Tail.sumHelper`が基底の場合に達すると、制御は{anchorName TailSum}`Tail.sum`に直接戻せる。途中の{anchorName TailSum}`Tail.sumHelper`の呼び出しは、再帰呼び出しの結果をそのまま返すだけだからである。
言い換えれば、{anchorName TailSum}`Tail.sumHelper`の再帰呼び出しごとに一つのスタックフレームを使い回せる。
末尾呼び出しの除去とはまさにこのスタックフレームの使い回しであり、{anchorName TailSum}`Tail.sumHelper`を*末尾再帰関数*と呼ぶ。

{anchorName TailSum}`Tail.sumHelper`の一つ目の引数には、そうでなければ呼び出しスタックで追跡する必要がある情報、つまりそれまでに出会った数の和がすべて入っている。
再帰呼び出しごとに、呼び出しスタックに新しい情報を加えるのではなく、この引数が新しい情報で更新される。
{anchorName TailSum}`soFar`のように呼び出しスタックからの情報を置き換える引数を*アキュムレータ*と呼ぶ。

執筆時点で著者の計算機では、{anchorName NonTailSum}`NonTail.sum`は216,856以上の要素を持つリストを渡すとスタックオーバーフローで落ちる。
一方、{anchorName TailSum}`Tail.sum`はスタックオーバーフローなしに100,000,000要素のリストを足せる。
{anchorName TailSum}`Tail.sum`を動かす間は新しいスタックフレームを積む必要がないので、現在のリストを持つ可変変数を伴う{kw}`while`ループとまったく等価である。
再帰呼び出しごとに、スタック上の関数の引数が単にリストの次の節点で置き換えられる。


# 末尾の位置とそうでない位置
%%%
tag := "tail-positions"
%%%

{anchorName TailSum}`Tail.sumHelper`が末尾再帰であるのは、再帰呼び出しが*末尾の位置*にあるためである。
非形式的に言えば、関数呼び出しは、呼び出し側が返された値を何らかの形で変更する必要がなく、単にそれを直接返すときに末尾の位置にある。
より形式的には、末尾の位置は式について明示的に定義できる。

{kw}`match`式が末尾の位置にあるなら、その各枝も末尾の位置にある。
{kw}`match`が枝を選んだら、制御はすぐにそこへ進む。
同様に、{kw}`if`式自体が末尾の位置にあるなら、その両方の枝も末尾の位置にある。
最後に、{kw}`let`式が末尾の位置にあるなら、その本体もそうである。

他の位置はすべて末尾の位置ではない。
関数やコンストラクタの引数は末尾の位置ではない。評価は、その引数の値に適用される関数やコンストラクタを追跡せねばならないためである。
内側の関数の本体は末尾の位置ではない。制御がそこへ渡ることすらないかもしれないためである。関数の本体は、その関数が呼ばれるまで評価されない。
同様に、関数型の本体も末尾の位置ではない。
{lit}`(x : α) → E`の{lit}`E`を評価するには、得られる型に{lit}`(x : α) → ...`を巻き付けねばならないことを追跡する必要がある。

{anchorName NonTailSum}`NonTail.sum`では、再帰呼び出しは{anchorTerm NonTailSum}`+`の引数なので末尾の位置ではない。
{anchorName TailSum}`Tail.sumHelper`では、再帰呼び出しはパターンマッチングのすぐ下にあり、そのパターンマッチング自体が関数の本体なので、末尾の位置にある。

執筆時点で、Leanは再帰関数における直接の末尾呼び出しだけを除去する。
つまり、{lit}`f`の定義における{lit}`f`への末尾呼び出しは除去されるが、別の関数{lit}`g`への末尾呼び出しは除去されない。
別の関数への末尾呼び出しを除去してスタックフレームを節約することはもちろん可能だが、Leanにはまだ実装されていない。

# リストの反転
%%%
tag := "reversing-lists-tail-recursively"
%%%

{anchorName NonTailReverse}`NonTail.reverse`関数は、各部分リストの先頭を結果の末尾に付けることでリストを反転する。

```anchor NonTailReverse
def NonTail.reverse : List α → List α
  | [] => []
  | x :: xs => reverse xs ++ [x]
```
これを使って{anchorTerm NonTailReverseSteps}`[1, 2, 3]`を反転すると、次の段階の並びになる。
```anchorEvalSteps NonTailReverseSteps
NonTail.reverse [1, 2, 3]
===>
(NonTail.reverse [2, 3]) ++ [1]
===>
((NonTail.reverse [3]) ++ [2]) ++ [1]
===>
(((NonTail.reverse []) ++ [3]) ++ [2]) ++ [1]
===>
(([] ++ [3]) ++ [2]) ++ [1]
===>
([3] ++ [2]) ++ [1]
===>
[3, 2] ++ [1]
===>
[3, 2, 1]
```

末尾再帰の版は、各段階でアキュムレータに対して{lit}`· ++ [x]`ではなく{lit}`x :: ·`を使う。

```anchor TailReverse
def Tail.reverseHelper (soFar : List α) : List α → List α
  | [] => soFar
  | x :: xs => reverseHelper (x :: soFar) xs

def Tail.reverse (xs : List α) : List α :=
  Tail.reverseHelper [] xs
```
これは、{anchorName NonTailReverse}`NonTail.reverse`で計算する間に各スタックフレームに保存された文脈が、基底の場合から順に適用されるためである。
「覚えられた」文脈の各部分は、後入れ先出しの順に実行される。
一方、アキュムレータを渡す版は、元の基底の場合ではなく、リストの最初の要素からアキュムレータを変更する。次の簡約の段階の並びに見られる。
```anchorEvalSteps TailReverseSteps
Tail.reverse [1, 2, 3]
===>
Tail.reverseHelper [] [1, 2, 3]
===>
Tail.reverseHelper [1] [2, 3]
===>
Tail.reverseHelper [2, 1] [3]
===>
Tail.reverseHelper [3, 2, 1] []
===>
[3, 2, 1]
```
言い換えれば、末尾再帰でない版は基底の場合から始まり、リストを右から左へと再帰の結果を変更していく。
リストの要素は、先入れ先出しの順にアキュムレータに影響する。
アキュムレータを使う末尾再帰の版は、リストの先頭から始まり、初期のアキュムレータの値をリストに沿って左から右へ変更していく。

加法は可換なので、{anchorName TailSum}`Tail.sum`ではこのことを考慮して何かをする必要がなかった。
リストの連結は可換ではないので、逆の向きで走らせても同じ効果を持つ演算を見つけるよう注意せねばならない。
{anchorName NonTailReverse}`NonTail.reverse`で再帰の結果の後に{anchorTerm NonTailReverse}`[x]`を付けるのは、結果を逆の順で組み立てるときに{anchorName NonTailReverse}`x`をリストの先頭に加えることに相当する。

# 複数の再帰呼び出し
%%%
tag := "multiple-call-tail-recursion"
%%%

{anchorName mirrorNew (module := Examples.Monads.Conveniences)}`BinTree.mirror`の定義には再帰呼び出しが二つある。

```anchor mirrorNew (module := Examples.Monads.Conveniences)
def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)
```
命令型言語が{anchorName NonTailReverse}`reverse`や{anchorName NonTailSum}`sum`のような関数に通常whileループを使うのと同じく、この種のたどり方には通常再帰関数を使う。
この関数は、アキュムレータを渡す流儀を使って素直に末尾再帰に書き直すことはできない。少なくともこの本で紹介した技法では無理である。

通常、再帰の各段階に複数の再帰呼び出しが必要なら、アキュムレータを渡す流儀を使うのは難しい。
この難しさは、再帰関数をループと明示的なデータ構造を使う形に書き直す難しさに似ており、さらにLeanに関数が停止することを納得させる面倒が加わる。
しかし、{anchorName mirrorNew (module:=Examples.Monads.Conveniences)}`BinTree.mirror`のように、複数の再帰呼び出しはしばしば、自分自身が複数回再帰的に現れるコンストラクタを持つデータ構造を示している。
このような場合、その構造の深さは全体の大きさに対してしばしば対数的であり、スタックとヒープの間の取り替えの差はそれほど厳しくない。
これらの関数を末尾再帰にする体系的な技法として、*継続渡しの流儀*や*脱関数化*を使うものがあるが、それらはこの本の範囲外である。

# 練習問題
%%%
tag := "tail-recursion-exercises"
%%%

次の末尾再帰でない関数をそれぞれ、アキュムレータを渡す末尾再帰関数に書き換えよ。


```anchor NonTailLength
def NonTail.length : List α → Nat
  | [] => 0
  | _ :: xs => NonTail.length xs + 1
```


```anchor NonTailFact
def NonTail.factorial : Nat → Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)
```

{anchorName NonTailFilter}`NonTail.filter`の書き換えは、末尾再帰によりスタックの空間が一定で、入力のリストの長さに線形な時間のプログラムになるべきである。
元のものに対する定数倍の負担は許容される。

```anchor NonTailFilter
def NonTail.filter (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs =>
    if p x then
      x :: filter p xs
    else
      filter p xs
```
