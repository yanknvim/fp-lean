module
public import VersoManual
import FPLean.Examples


open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "FelineLib"


#doc (Manual) "Additional Conveniences" =>
%%%
tag := "hello-world-conveniences"
%%%

# 入れ子のアクション
%%%
tag := "nested-actions"
%%%

:::paragraph
{lit}`feline`の関数の多くには、{anchorName dump}`IO`アクションの結果に名前を付け、それをすぐ一度だけ使う、という繰り返しの形が現れる。
たとえば{moduleName}`dump`では、
```anchor dump
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream
```

{moduleName (anchor:=stdoutBind)}`stdout`についてこの形が現れる。
```anchor stdoutBind
    let stdout ← IO.getStdout
    stdout.write buf
```

同様に、{moduleName}`fileStream`には次の部分がある。
```anchor fileExistsBind
  let fileExists ← filename.pathExists
  if not fileExists then
```
:::

:::paragraph
Leanが{moduleTerm}`do`ブロックをコンパイルするとき、括弧の直下にある左矢印から成る式は、最も内側の{moduleTerm}`do`へ持ち上げられ、その結果は一意な名前に対応付けられる。
この一意な名前が、その式があった場所を置き換える。
つまり、{moduleName (module := Examples.Cat)}`dump`は次のようにも書ける。

```anchor dump (module:=Examples.Cat)
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    (← IO.getStdout).write buf
    dump stream
```

この版の{anchorName dump (module := Examples.Cat)}`dump`は、一度しか使わない名前を導入せずに済み、プログラムがかなり簡単になる。
Leanが入れ子になった式の文脈から持ち上げる{moduleName (module := Examples.Cat)}`IO`アクションを*入れ子のアクション*と呼ぶ。
:::

:::paragraph
{moduleName (module := Examples.Cat)}`fileStream`も同じ手法で簡単にできる。

```anchor fileStream (module := Examples.Cat)
def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  if not (← filename.pathExists) then
    (← IO.getStderr).putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))
```

この場合、{anchorName fileStream (module := Examples.Cat)}`handle`というローカル名も入れ子のアクションで消せるが、そうすると式が長く複雑になる。
入れ子のアクションを使うのがよいスタイルであることは多いが、途中の結果に名前を付けた方が役に立つこともある。
:::

ただし、入れ子のアクションは、周囲の{moduleTerm (module := Examples.Cat)}`do`ブロックの中にある{moduleName (module := Examples.Cat)}`IO`アクションの短い書き方にすぎないことを覚えておきたい。
それらを実行する際の副作用はやはり同じ順序で起こり、副作用の実行が式の評価に混ざることはない。
したがって、入れ子のアクションを{kw}`if`の枝から持ち上げることはできない。

これが紛らわしくなる例として、実行されたことを世間に知らせてからデータを返す、次の補助的な定義を考える。

```anchor getNumA (module := Examples.Cat)
def getNumA : IO Nat := do
  (← IO.getStdout).putStrLn "A"
  pure 5
```

```anchor getNumB (module := Examples.Cat)
def getNumB : IO Nat := do
  (← IO.getStdout).putStrLn "B"
  pure 7
```

これらの定義は、利用者の入力を検証したり、データベースを読んだり、ファイルを開いたりする、もっと複雑な{anchorName getNumB (module:=Examples.Cat)}`IO`コードの代わりである。

数Aが5なら{moduleTerm (module := Examples.Cat)}`0`を、そうでなければ数Bを表示するプログラムは、次のように書くかもしれない。

```anchor testEffects (module := Examples.Cat)
def test : IO Unit := do
  let a : Nat := if (← getNumA) == 5 then 0 else (← getNumB)
  (← IO.getStdout).putStrLn s!"The answer is {a}"
```

このプログラムは次と等価である。

```anchor testEffectsExpanded (module := Examples.Cat)
def test : IO Unit := do
  let x ← getNumA
  let y ← getNumB
  let a : Nat := if x == 5 then 0 else y
  (← IO.getStdout).putStrLn s!"The answer is {a}"
```

これは、{moduleName (module := Examples.Cat)}`getNumA`の結果が{moduleTerm (module := Examples.Cat)}`5`に等しいかどうかに関係なく{moduleName (module := Examples.Cat)}`getNumB`を実行してしまう。
この混乱を防ぐため、{moduleTerm (module := Examples.Cat)}`do`の行そのものではない{kw}`if`の中では入れ子のアクションを使えず、次のエラーメッセージになる。

```anchorError testEffects (module := Examples.Cat)
Nested action `← getNumB` must be nested inside a `do` expression.
```


# {lit}`do`の柔軟なレイアウト
%%%
tag := "do-layout-syntax"
%%%

Leanでは、{moduleTerm (module := Examples.Cat)}`do`式は空白に敏感である。
{moduleTerm (module := Examples.Cat)}`do`の中の{moduleName (module := Examples.Cat)}`IO`アクションやローカル束縛は、それぞれ自分の行から始め、すべて同じインデントにする。
{moduleTerm (module := Examples.Cat)}`do`のほとんどは、このように書くべきである。
ただし、まれに空白とインデントを手で制御する必要がある場合や、小さなアクションを複数1行にまとめると便利な場合がある。
そのような場合は、改行をセミコロンで、インデントを淡括弧で置き換えられる。

たとえば、次のプログラムはすべて等価である。

```anchor helloOne (module := Examples.Cat)
-- This version uses only whitespace-sensitive layout
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let name := (← stdin.getLine).trimAscii
  stdout.putStrLn s!"Hello, {name}!"
```

```anchor helloTwo (module := Examples.Cat)
-- This version is as explicit as possible
def main : IO Unit := do {
  let stdin ← IO.getStdin;
  let stdout ← IO.getStdout;

  stdout.putStrLn "How would you like to be addressed?";
  let name := (← stdin.getLine).trimAscii;
  stdout.putStrLn s!"Hello, {name}!"
}
```

```anchor helloThree (module := Examples.Cat)
-- This version uses a semicolon to put two actions on the same line
def main : IO Unit := do
  let stdin ← IO.getStdin; let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let name := (← stdin.getLine).trimAscii
  stdout.putStrLn s!"Hello, {name}!"
```


慣用的なLeanのコードでは、{moduleTerm (module := Examples.Cat)}`do`に淡括弧を使うことはほとんどない。

# {kw}`#eval`で{lit}`IO`アクションを実行する
%%%
tag := "eval-io"
%%%

Leanの{moduleTerm (module := Examples.Cat)}`#eval`コマンドは、{moduleName (module := Examples.Cat)}`IO`アクションを評価するだけでなく実行するのにも使える。
通常、Leanのファイルに{moduleTerm (module := Examples.Cat)}`#eval`コマンドを書くと、Leanは与えられた式を評価し、その値を文字列に変換して、ツールチップと情報ウィンドウに表示する。
{moduleName (module := Examples.Cat)}`IO`アクションは文字列に変換できないからといって失敗するのではなく、{moduleTerm (module := Examples.Cat)}`#eval`はそれを実行し、副作用を起こす。
実行の結果が{moduleName (module := Examples.Cat)}`Unit`の値{moduleTerm (module := Examples.Cat)}`()`なら結果の文字列は表示されないが、文字列に変換できる型なら、Leanは得られた値を表示する。

:::paragraph
つまり、先ほどの{moduleName (module := Examples.HelloWorld)}`countdown`と{moduleName (module := Examples.HelloWorld)}`runActions`の定義があれば、

```anchor evalDoesIO (module := Examples.HelloWorld)
#eval runActions (countdown 3)
```

と表示される。

```anchorInfo evalDoesIO (module := Examples.HelloWorld)
3
2
1
Blast off!
```
:::

これは、{moduleName (module := Examples.HelloWorld)}`IO`アクションそのものの分かりにくい表現ではなく、そのアクションを実行して得られる出力である。
言い換えれば、{moduleName (module := Examples.HelloWorld)}`IO`アクションに対して、{moduleTerm (module := Examples.HelloWorld)}`#eval`は与えられた式を*評価*し、得られたアクションの値を*実行*する。

{moduleName (module := Examples.HelloWorld)}`IO`アクションを{moduleTerm (module := Examples.HelloWorld)}`#eval`で手早く試すのは、プログラム全体をコンパイルして実行するよりずっと便利なことが多い。
ただし、いくつか制限がある。
たとえば、標準入力からの読み込みは、単に空の入力を返す。
さらに、Leanが利用者に提供する診断情報を更新する必要があるたびに、{moduleName (module := Examples.HelloWorld)}`IO`アクションが再実行される。これは予測できない時点で起こりうる。
たとえば、ファイルを読み書きするアクションが、予期しないときに読み書きしてしまうことがある。
