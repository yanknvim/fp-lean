module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.MonadTransformers.Conveniences"

#doc (Manual) "Additional Conveniences" =>
%%%
tag := "monad-transformer-conveniences"
%%%

# パイプ演算子
%%%
tag := "pipe-operators"
%%%

関数は通常、その引数の前に書く。
プログラムを左から右へ読むとき、これは関数の*出力*を最重要視する見方を促す。関数には達成すべき目標（つまり計算すべき値）があり、その過程を支えるために引数を受け取るのである。
しかし、ある種のプログラムは、出力を生み出すために入力が次々と洗練されていく、という見方のほうが理解しやすい。
そうした場合のために、LeanはF#が提供するものに似た*パイプライン*演算子を用意している。
パイプ演算子は、Clojureのスレッディングマクロと同じ場面で役に立つ。

パイプライン{anchorTerm pipelineShort}`E₁ |> E₂`は{anchorTerm pipelineShort}`E₂ E₁`の略である。
たとえば、次を評価すると、
```anchor some5
#eval some 5 |> toString
```
次の結果になる。
```anchorInfo some5
"(some 5)"
```
この重点の移し方がプログラムを読みやすくすることもあるが、パイプラインは多くの部品を含むときに真価を発揮する。

次の定義があるとき、

```anchor times3
def times3 (n : Nat) : Nat := n * 3
```
次のパイプラインは、
```anchor itIsFive
#eval 5 |> times3 |> toString |> ("It is " ++ ·)
```
次のようになる。
```anchorInfo itIsFive
"It is 15"
```
より一般に、パイプラインの並び{anchorTerm pipeline}`E₁ |> E₂ |> E₃ |> E₄`は、入れ子になった関数適用{anchorTerm pipeline}`E₄ (E₃ (E₂ E₁))`の略である。

パイプラインは逆向きにも書ける。
この場合、データ変換の対象が先頭には来ないが、多くの入れ子になった括弧が読み手にとって負担になる場合には、適用の段階が分かりやすくなる。
先ほどの例は次のようにも等価に書ける。
```anchor itIsAlsoFive
#eval ("It is " ++ ·) <| toString <| times3 <| 5
```
これは次の略である。
```anchor itIsAlsoFiveParens
#eval ("It is " ++ ·) (toString (times3 5))
```

ドットの前に型の名前を置いてドットの後の演算子の名前空間を解決する、Leanのメソッドのドット記法も、パイプラインと似た役割を果たす。
パイプ演算子がなくても、{anchorTerm listReverse}`List.reverse [1, 2, 3]`の代わりに{anchorTerm listReverse}`[1, 2, 3].reverse`と書ける。
しかし、パイプ演算子は、ドット付きの関数を多く使うときにも役に立つ。
{anchorTerm listReverseDropReverse}`([1, 2, 3].reverse.drop 1).reverse`は{anchorTerm listReverseDropReverse}`[1, 2, 3] |> List.reverse |> List.drop 1 |> List.reverse`とも書ける。
この版では、引数を取るというだけで式を括弧で囲む必要がなくなり、KotlinやC#のような言語のメソッド呼び出しの連鎖の便利さが戻ってくる。
しかし、名前空間を手で与える必要はまだある。
最後の便利さとして、Leanは「パイプラインのドット」演算子を用意している。パイプラインのように関数をまとめるが、名前空間の解決に型の名前を使う。
「パイプラインのドット」を使うと、この例は{anchorTerm listReverseDropReversePipe}`[1, 2, 3] |>.reverse |>.drop 1 |>.reverse`に書き直せる。

# 無限ループ
%%%
tag := "infinite-loops"
%%%

{kw}`do`ブロックの中では、{kw}`repeat`キーワードが無限ループを導入する。
たとえば、文字列{anchorTerm spam}`"Spam!"`を連呼するプログラムはこれを使える。

```anchor spam
def spam : IO Unit := do
  repeat IO.println "Spam!"
```
{kw}`repeat`ループは{kw}`for`ループと同じく{kw}`break`と{kw}`continue`を支える。

{ref "streams"}[{lit}`feline`の実装]にある{anchorName dump (module := FelineLib)}`dump`関数は、再帰関数を使って永遠に動く。
```anchor dump (module := FelineLib)
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream
```
この関数は{kw}`repeat`を使うと大幅に短くできる。

```anchor dump
def dump (stream : IO.FS.Stream) : IO Unit := do
  let stdout ← IO.getStdout
  repeat do
    let buf ← stream.read bufsize
    if buf.isEmpty then break
    stdout.write buf
```

{anchorName spam}`spam`も{anchorName dump}`dump`も{kw}`partial`として宣言する必要がない。それ自体が無限に再帰しているわけではないためである。
代わりに、{kw}`repeat`は{anchorTerm names}`ForM`インスタンスが{kw}`partial`である型を使う。
partial は呼び出す側の関数に「感染」しない。

# whileループ
%%%
tag := "while-loops"
%%%

局所的な可変性を使ってプログラミングするときは、{kw}`while`ループが、{kw}`if`で守られた{kw}`break`を伴う{kw}`repeat`の便利な代わりになる。

```anchor dumpWhile
def dump (stream : IO.FS.Stream) : IO Unit := do
  let stdout ← IO.getStdout
  let mut buf ← stream.read bufsize
  while not buf.isEmpty do
    stdout.write buf
    buf ← stream.read bufsize
```
裏では、{kw}`while`は{kw}`repeat`のより単純な記法にすぎない。
