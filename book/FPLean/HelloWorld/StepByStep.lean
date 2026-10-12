module
public import VersoManual
import FPLean.Examples


open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "HelloName"

example_module Examples.HelloWorld



#doc (Manual) "Step By Step" =>
%%%
tag := "step-by-step"
%%%

:::paragraph
{moduleTerm}`do`ブロックは、1行ずつ実行できる。
前の節のプログラムから始める。

```anchor block1
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropEndWhile Char.isWhitespace
  stdout.putStrLn s!"Hello, {name}!"
```
:::

# 標準入出力
%%%
tag := "stdio"
%%%

:::paragraph
最初の行は{anchor line1}`let stdin ← IO.getStdin`であり、残りは次のとおりである。
```anchor block2
  let stdout ← IO.getStdout
  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropEndWhile Char.isWhitespace
  stdout.putStrLn s!"Hello, {name}!"
```
:::

{anchorTerm block2}`←`を使う{kw}`let`文を実行するには、まず矢印の右の式（この場合は{moduleTerm}`IO.getStdin`）を評価する。
この式は単なる変数なので、その値が参照される。
得られた値は、組み込みの原始的な{moduleTerm}`IO`アクションである。
次の手順は、この{moduleTerm}`IO`アクションを実行することである。標準入力ストリームを表す{moduleTerm}`IO.FS.Stream`型の値が得られる。
そのあと、標準入力は{moduleTerm}`do`ブロックの残りにおいて、矢印の左の名前（ここでは{anchorTerm line1}`stdin`）に対応付けられる。

二番目の行{anchor line2}`let stdout ← IO.getStdout`の実行も同様に進む。
まず{moduleTerm}`IO.getStdout`という式が評価され、標準出力を返す{moduleTerm}`IO`アクションが得られる。
次にこのアクションが実行され、実際に標準出力が返る。
最後に、この値が{moduleTerm}`do`ブロックの残りにおいて名前{anchorTerm line2}`stdout`に対応付けられる。

# 質問する
%%%
tag := "asking-a-question"
%%%

:::paragraph
{anchorTerm line1}`stdin`と{anchorTerm line2}`stdout`が得られたので、ブロックの残りは質問と応答である。
```anchor block3
  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropEndWhile Char.isWhitespace
  stdout.putStrLn s!"Hello, {name}!"
```
:::

ブロックの最初の文{anchor line3}`stdout.putStrLn "How would you like to be addressed?"`は、式だけから成る。
式を実行するには、まずそれを評価する。
この場合、{moduleTerm}`IO.FS.Stream.putStrLn`の型は{moduleTerm}`IO.FS.Stream → String → IO Unit`である。
つまり、ストリームと文字列を受け取って{moduleTerm}`IO`アクションを返す関数である。
この式では、関数呼び出しに{ref "behind-the-scenes"}[アクセサ記法]を使っている。
この関数は、標準出力ストリームと文字列の二つの引数に適用される。
この式の値は、文字列と改行文字を出力ストリームに書き込む{moduleTerm}`IO`アクションである。
この値が得られたので、次の手順はそれを実行することである。これにより、文字列と改行が実際に{anchorTerm setup}`stdout`に書き込まれる。
式だけから成る文は、新しい変数を導入しない。

ブロックの次の文は{anchor line4}`let input ← stdin.getLine`である。
{moduleTerm}`IO.FS.Stream.getLine`の型は{moduleTerm}`IO.FS.Stream → IO String`であり、ストリームから、文字列を返す{moduleTerm}`IO`アクションへの関数である。
これもまたアクセサ記法の例である。
この{moduleTerm}`IO`アクションが実行され、利用者が入力行を最後まで打ち終えるまでプログラムは待つ。
利用者が「{lit}`David`」と入力したとする。
得られた行（{lit}`"David\n"`）が{anchorTerm block5}`input`に対応付けられる。エスケープシーケンス{lit}`\n`は改行文字を表す。

```anchor block5
  let name := input.dropEndWhile Char.isWhitespace
  stdout.putStrLn s!"Hello, {name}!"
```

:::paragraph
次の行{anchor line5}`let name := input.dropEndWhile Char.isWhitespace`は{kw}`let`文である。
このプログラムの他の{kw}`let`文と違い、{anchorTerm line4}`←`ではなく{anchorTerm block5}`:=`を使っている。
つまり、式は評価されるが、その値は{moduleTerm}`IO`アクションである必要はなく、実行もされない。
この場合、{moduleName}`String.dropEndWhile`は文字列と{ref "string-matching"}[パターン]を受け取り、文字列の末尾にあってパターンに一致する部分文字列をすべて取り除いた{tech}[文字列スライス]を返す。
たとえば、

```anchorTerm dropBang (module := Examples.HelloWorld)
#eval "Hello!!!".dropEndWhile (· == '!')
```

が得られる。

```anchorInfo dropBang (module := Examples.HelloWorld)
Hello
```

また、

```anchorTerm dropNonLetter (module := Examples.HelloWorld)
#eval "Hello...   ".dropEndWhile (fun c => not (c.isAlphanum))
```

が得られる。

```anchorInfo dropNonLetter (module := Examples.HelloWorld)
Hello
```

文字列の右側から英数字以外の文字がすべて取り除かれている。
プログラムのこの行では、入力文字列の右側から空白文字（改行を含む）が取り除かれ、{lit}`David`が得られる。これがブロックの残りで{anchorTerm block5}`name`に対応付けられる。
:::

# 利用者に挨拶する
%%%
tag := "greeting"
%%%

:::paragraph
{moduleTerm}`do`ブロックで残っているのは、一つの文だけである。
```anchor line6
  stdout.putStrLn s!"Hello, {name}!"
```
:::

{anchorTerm line6}`putStrLn`に渡す文字列は文字列補間で組み立てられ、{moduleTerm (module := Examples.HelloWorld)}`"Hello, David!"`という文字列になる。
この文は式なので評価され、この文字列を改行付きで標準出力に表示する{moduleTerm}`IO`アクションが得られる。
式の評価が終わると、得られた{moduleTerm}`IO`アクションが実行され、挨拶が表示される。

# 値としての{lit}`IO`アクション
%%%
tag := "actions-as-values"
%%%


ここまでの説明では、式の評価と{moduleTerm}`IO`アクションの実行を区別する必要がなぜあるのか、分かりにくいかもしれない。
どのアクションも、作られた直後に実行されているからである。
他の言語のように、評価の途中で副作用をそのまま起こせばよいのではないか。

理由は二つある。
第一に、評価と実行を分けると、どの関数が副作用を持ちうるかをプログラムに明示させられる。
副作用のない部分は、プログラマの頭の中でも、Leanの形式的な証明の仕組みを使う場合でも、数学的な推論に向いている。この分離により、誤りを避けやすくなる。
第二に、{moduleTerm}`IO`アクションができた時点ですべて実行しなければならないわけではない。
アクションに言及するだけで実行しないでおけるので、普通の関数を制御構造として使える。

:::paragraph
たとえば、関数{anchorName twice (module:=Examples.HelloWorld)}`twice`は{moduleTerm}`IO`アクションを引数に取り、そのアクションを二度実行する新しいアクションを返す。

```anchor twice (module := Examples.HelloWorld)
def twice (action : IO Unit) : IO Unit := do
  action
  action
```

次を実行すると、

```anchorTerm twiceShy (module := Examples.HelloWorld)
twice (IO.println "shy")
```

出力は次のようになる。

```anchorInfo twiceShy (module := Examples.HelloWorld)
shy
shy
```

と表示される。
これを一般化して、元のアクションを任意の回数実行する版も書ける。

```anchor nTimes (module := Examples.HelloWorld)
def nTimes (action : IO Unit) : Nat → IO Unit
  | 0 => pure ()
  | n + 1 => do
    action
    nTimes action n
```
:::

:::paragraph
{moduleTerm (module := Examples.HelloWorld)}`Nat.zero`の場合の結果は{moduleTerm (module := Examples.HelloWorld)}`pure ()`である。
関数{moduleTerm (module := Examples.HelloWorld)}`pure`は、副作用を持たず、{moduleTerm (module := Examples.HelloWorld)}`pure`の引数（この場合は{moduleTerm (module := Examples.HelloWorld)}`Unit`のコンストラクタ）を返す{moduleTerm (module := Examples.HelloWorld)}`IO`アクションを作る。
何もせず、意味のあるものも返さないアクションである{moduleTerm (module := Examples.HelloWorld)}`pure ()`は、退屈このうえないが、非常に役に立つ。
再帰の場合は、{moduleTerm (module := Examples.HelloWorld)}`do`ブロックを使って、まず{moduleTerm (module := Examples.HelloWorld)}`action`を実行し、次に再帰呼び出しの結果を実行するアクションを作る。
{anchor nTimes3 (module := Examples.HelloWorld)}`#eval nTimes (IO.println "Hello") 3`を実行すると、次の出力が得られる。

```anchorInfo nTimes3 (module := Examples.HelloWorld)
Hello
Hello
Hello
```

:::

:::paragraph
関数を制御構造として使えるほかに、{moduleTerm (module := Examples.HelloWorld)}`IO`アクションが第一級の値であることから、後で実行するためにデータ構造に入れておける。
たとえば、関数{moduleName (module := Examples.HelloWorld)}`countdown`は{moduleTerm (module := Examples.HelloWorld)}`Nat`を取り、まだ実行していない{moduleTerm (module := Examples.HelloWorld)}`IO`アクションのリストを、それぞれの{moduleTerm (module := Examples.HelloWorld)}`Nat`に対して一つずつ返す。

```anchor countdown (module := Examples.HelloWorld)
def countdown : Nat → List (IO Unit)
  | 0 => [IO.println "Blast off!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n
```

この関数には副作用がなく、何も表示しない。
たとえば、引数に適用して、得られたアクションのリストの長さを確かめられる。

```anchor from5  (module := Examples.HelloWorld)
def from5 : List (IO Unit) := countdown 5
```

このリストには六つの要素が入っている（各数の分と、0に対応する{moduleTerm (module := Examples.HelloWorld)}`"Blast off!"`アクションである）。

```anchorTerm from5length (module := Examples.HelloWorld)
#eval from5.length
```

```anchorInfo from5length (module := Examples.HelloWorld)
6
```

:::

:::paragraph
関数{moduleTerm (module := Examples.HelloWorld)}`runActions`はアクションのリストを取り、それらを順にすべて実行する一つのアクションを組み立てる。

```anchor runActions (module := Examples.HelloWorld)
def runActions : List (IO Unit) → IO Unit
  | [] => pure ()
  | act :: actions => do
    act
    runActions actions
```

その構造は{moduleName (module := Examples.HelloWorld)}`nTimes`とほぼ同じである。違いは、{moduleName (module := Examples.HelloWorld)}`Nat.succ`ごとに一つのアクションを実行する代わりに、{moduleName (module := Examples.HelloWorld)}`List.cons`の下にあるアクションを実行する点である。
同様に、{moduleName (module := Examples.HelloWorld)}`runActions`自身はアクションを実行しない。
それらを実行する新しいアクションを作るので、そのアクションを{moduleName (module := Examples.HelloWorld)}`main`の一部として実行される位置に置く必要がある。

```anchor main (module := Examples.HelloWorld)
def main : IO Unit := runActions from5
```

このプログラムを実行すると、次の出力が得られる。

```commands countdownFromFive ""
$ countdown
5
4
3
2
1
Blast off!
```

:::

:::paragraph
このプログラムを実行すると、何が起こるか。
まず{moduleName (module := Examples.HelloWorld)}`main`を評価する。これは次のように進む。

```anchorEvalSteps evalMain  (module := Examples.HelloWorld)
main
===>
runActions from5
===>
runActions (countdown 5)
===>
runActions
  [IO.println "5",
   IO.println "4",
   IO.println "3",
   IO.println "2",
   IO.println "1",
   IO.println "Blast off!"]
===>
do IO.println "5"
   IO.println "4"
   IO.println "3"
   IO.println "2"
   IO.println "1"
   IO.println "Blast off!"
   pure ()
```

得られた{moduleTerm (module := Examples.HelloWorld)}`IO`アクションは{moduleTerm (module := Examples.HelloWorld)}`do`ブロックである。
次に、その{moduleTerm (module := Examples.HelloWorld)}`do`ブロックの各手順を一つずつ実行し、期待どおりの出力が得られる。
最後の{moduleTerm (module := Examples.HelloWorld)}`pure ()`には副作用がなく、{moduleTerm (module := Examples.HelloWorld)}`runActions`の定義に基底ケースが必要なために置かれているだけである。
:::

# 練習問題
%%%
tag := "step-by-step-exercise"
%%%

:::paragraph
次のプログラムの実行を紙の上で一歩ずつたどってみよ。

```anchor ExMain (module := Examples.HelloWorld)
def main : IO Unit := do
  let englishGreeting := IO.println "Hello!"
  IO.println "Bonjour!"
  englishGreeting
```

実行をたどりながら、どこで式が評価され、どこで{moduleTerm (module := Examples.HelloWorld)}`IO`アクションが実行されるのかを見分けよ。
{moduleTerm (module := Examples.HelloWorld)}`IO`アクションの実行で副作用が起きるなら、それを書き留めよ。
それが終わったら、Leanでプログラムを実行し、副作用についての予想が正しかったかを確かめよ。
:::
