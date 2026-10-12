module
public import VersoManual
import FPLean.Examples


open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"

set_option verso.exampleModule "FelineLib"

example_module Examples.Cat

#doc (Manual) "Worked Example: {lit}`cat`" =>
%%%
tag := "example-cat"
%%%

標準的なUnixのユーティリティ{lit}`cat`は、いくつかのコマンドラインオプションと、0個以上の入力ファイルを取る。
ファイルが指定されない場合、または指定されたファイルがダッシュ（{lit}`-`）である場合は、ファイルを読む代わりに標準入力をその入力とする。
入力の内容は、順に標準出力へ書き出される。
指定された入力ファイルが存在しない場合は標準エラーにその旨を出力し、{lit}`cat`は残りの入力の連結を続ける。
入力ファイルのどれかが存在しない場合、終了コードは0以外になる。

この節では、{lit}`cat`を単純化した{lit}`feline`というプログラムを扱う。
よく使われる{lit}`cat`と違い、{lit}`feline`には、行番号を付けたり、表示できない文字を示したり、ヘルプを表示したりするためのコマンドラインオプションはない。
さらに、端末に関連付けられた標準入力からは一度しか読み込めない。

この節から最大限の学びを得るには、手を動かしながら読み進めるとよい。
コード例をコピー＆ペーストしても構わないが、手で打ち込む方がよい。
そうすれば、コードを打ち込み、誤りから立ち直り、コンパイラのフィードバックを読み取るという一連の流れを身につけやすい。

# 準備
%%%
tag := "example-cat-start"
%%%

{lit}`feline`を実装する最初の一歩は、パッケージを作り、コードの構成を決めることである。
このプログラムはごく単純なので、コードはすべて{lit}`Main.lean`に置く。
まず{lit}`lake new feline`を実行する。
Lakefileを編集してライブラリの部分を削除し、生成されたライブラリのコードと{lit}`Main.lean`からの参照も削除する。
ここまで終えると、{lit}`lakefile.toml`は次のようになる。

```plainFile "feline/1/lakefile.toml"
name = "feline"
version = "0.1.0"
defaultTargets = ["feline"]

[[lean_exe]]
name = "feline"
root = "Main"
```

また{lit}`Main.lean`は次のようになる。
```plainFile "feline/1/Main.lean"
def main : IO Unit :=
  IO.println s!"Hello, cats!"
```
あるいは、{lit}`lake new feline exe`を実行すると、ライブラリの節を含まないテンプレートを使うよう{lit}`lake`に指示できるので、ファイルを編集する必要がない。

{command feline1 "feline/1"}`lake build`を実行して、コードがビルドできることを確かめる。


# ストリームの連結
%%%
tag := "example-cat-streams"
%%%

プログラムの基本的な骨組みができたので、いよいよコードを書いていく。
まともな{lit}`cat`の実装は{lit}`/dev/random`のような無限のIOストリームにも使えるので、入力をすべてメモリに読み込んでから出力するわけにはいかない。
さらに、1文字ずつ処理するとひどく遅くなるので、そうするべきでもない。
代わりに、連続したデータのブロックを一度に読み込み、ブロック単位で標準出力に送るのがよい。

まず、読み込むブロックの大きさを決める。
簡単のため、この実装では控えめに20キロバイトのブロックを使う。
{anchorName bufsize}`USize`はCの{c}`size_t`に相当する。配列の有効な大きさをすべて表せる符号なし整数型である。
```module (anchor:=bufsize)
def bufsize : USize := 20 * 1024
```


## ストリーム
%%%
tag := "streams"
%%%

{lit}`feline`の主要な処理は{anchorName dump}`dump`が担う。入力の終わりに達するまでブロック単位で読み込み、結果を標準出力に書き出す。
入力の終わりは、{anchorName dump}`read`が空のバイト配列を返すことで示される。
```module (anchor:=dump)
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream
```

関数{anchorName dump}`dump`は{anchorTerm dump}`partial`として宣言されている。引数よりすぐに小さいとは限らない入力に対して自分自身を再帰的に呼び出すためである。
関数をpartialとして宣言すると、Leanは停止性の証明を要求しない。
一方で、partialな関数は正しさの証明にはずっと向かない。Leanの論理で無限ループを許すと矛盾が生じるためである。
しかし、{anchorName dump}`dump`が停止することを証明する方法はない。{lit}`/dev/random`のような無限の入力では、実際には停止しないからである。
このような場合は、その関数を{anchorTerm dump}`partial`として宣言するしかない。

型{anchorName dump}`IO.FS.Stream`はPOSIXのストリームを表す。
舞台裏では、POSIXのストリーム操作ごとに一つのフィールドを持つ構造体として表されている。
各操作は、対応する処理を行うIOアクションとして表される。

```anchor Stream (module := Examples.Cat)
structure Stream where
  flush   : IO Unit
  read    : USize → IO ByteArray
  write   : ByteArray → IO Unit
  getLine : IO String
  putStr  : String → IO Unit
  isTty   : BaseIO Bool
```

型{anchorName Stream (module:=Examples.Cat)}`BaseIO`は{anchorName Stream (module:=Examples.Cat)}`IO`の一種で、実行時エラーを排除したものである。
Leanコンパイラには、標準入力、標準出力、標準エラーを表すストリームを得るための{anchorName Stream (module:=Examples.Cat)}`IO`アクション（{anchorName dump}`dump`で呼んでいる{anchorName dump}`IO.getStdout`など）が用意されている。
これらが普通の定義ではなく{anchorName Stream (module:=Examples.Cat)}`IO`アクションなのは、Leanがプロセス内でこれらの標準POSIXストリームを差し替えられるようにしているためである。おかげで、独自の{anchorName dump}`IO.FS.Stream`を書いてプログラムの出力を文字列に取り込む、といったことができる。

{anchorName dump}`dump`の制御の流れは、本質的には{lit}`while`ループである。
{anchorName dump}`dump`が呼ばれたとき、ストリームがファイルの終わりに達していれば、{anchorTerm dump}`pure ()`が{anchorName dump}`Unit`のコンストラクタを返して関数を終える。
まだファイルの終わりに達していなければ、ブロックを一つ読み込み、その内容を{anchorName dump}`stdout`に書き、その後で{anchorName dump}`dump`が自分自身を直接呼び出す。
再帰呼び出しは、{anchorTerm dump}`stream.read`が空のバイト配列を返してファイルの終わりを示すまで続く。

{anchorName dump}`dump`のように{kw}`do`の中の文として{kw}`if`式が現れるとき、{kw}`if`の各枝には暗黙に{kw}`do`が付けられる。
言い換えれば、{kw}`else`に続く手順の並びは、先頭に{kw}`do`があるのと同じように、実行すべき{anchorName dump}`IO`アクションの並びとして扱われる。
{kw}`if`の枝の中で{kw}`let`で導入した名前は、その枝の中でしか見えず、{kw}`if`の外では使えない。

{anchorName dump}`dump`を呼び続けてもスタックを使い切る危険はない。再帰呼び出しが関数の最後の手順として行われ、その結果を加工したり計算に使ったりせずそのまま返すからである。
この形の再帰を*末尾再帰*と呼び、{ref "tail-recursion"}[本書の後半]で詳しく説明する。
コンパイルされたコードが状態を保持する必要がないので、Leanコンパイラは再帰呼び出しをジャンプにコンパイルできる。

{lit}`feline`が標準入力を標準出力に流すだけなら、{anchorName dump}`dump`で十分である。
しかし、コマンドライン引数で渡されたファイルを開き、その内容を出力する必要もある。
引数が存在するファイルの名前なら、{anchorName fileStream}`fileStream`はそのファイルの内容を読むストリームを返す。
引数がファイルでない場合、{anchorName fileStream}`fileStream`はエラーを出して{anchorName fileStream}`none`を返す。
```module (anchor:=fileStream)
def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))
```

ファイルをストリームとして開くには二つの段階がある。
まず、ファイルを読み込みモードで開いてファイルハンドルを作る。
Leanのファイルハンドルは、基になるファイル記述子を追跡する。
ファイルハンドルの値への参照がなくなると、ファイナライザがファイル記述子を閉じる。
次に、{anchorName fileStream}`IO.FS.Stream.ofHandle`を使って、ファイルハンドルにPOSIXのストリームと同じインターフェースを与える。これは{anchorName Names}`Stream`構造体の各フィールドを、ファイルハンドルに対して働く対応する{anchorName fileStream}`IO`アクションで埋める。

## 入力の処理
%%%
tag := "handling-input"
%%%

{lit}`feline`の主ループは、{anchorName process}`process`という別の末尾再帰関数である。
入力のどれかが読めなかった場合に0以外の終了コードを返すため、{anchorName process}`process`はプログラム全体の現在の終了コードを表す引数{anchorName process}`exitCode`を取る。
さらに、処理すべき入力ファイルのリストを取る。
```module (anchor:=process)
def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with
  | [] => pure exitCode
  | "-" :: args =>
    let stdin ← IO.getStdin
    dump stdin
    process exitCode args
  | filename :: args =>
    let stream ← fileStream ⟨filename⟩
    match stream with
    | none =>
      process 1 args
    | some stream =>
      dump stream
      process exitCode args
```

{kw}`if`と同じく、{kw}`do`の中の文として使われる{kw}`match`の各枝にも、暗黙にそれぞれの{kw}`do`が付けられる。

場合分けは三つある。
一つは、処理すべきファイルがもう残っていない場合で、{anchorName process}`process`は終了コードをそのまま返す。
もう一つは、指定されたファイル名が{anchorTerm process}`"-"`の場合で、{anchorName process}`process`は標準入力の内容を出力してから、残りのファイル名を処理する。
最後は、実際のファイル名が指定された場合である。
この場合は{anchorName process}`fileStream`を使って、そのファイルをPOSIXのストリームとして開こうとする。
引数を{lit}`⟨ ... ⟩`で囲んでいるのは、{anchorName Names}`FilePath`が文字列を入れる単一フィールドの構造体だからである。
ファイルを開けなかった場合はそれを飛ばし、{anchorName process}`process`の再帰呼び出しで終了コードを{anchorTerm process}`1`にする。
開けた場合はそれを出力し、再帰呼び出しでは終了コードを変えない。

{anchorName process}`process`は構造的再帰なので、{kw}`partial`と付ける必要はない。
各再帰呼び出しには入力リストの残りが渡され、Leanのリストはすべて有限である。
したがって、{anchorName process}`process`が停止しないことはない。

## main
%%%
tag := "example-cat-main"
%%%

最後の手順は、{anchorName main}`main`アクションを書くことである。
これまでの例と違い、{lit}`feline`の{anchorName main}`main`は関数である。
Leanでは、{anchorName main}`main`は次の三つの型のいずれかを持つ。
 * {anchorTerm Names}`main : IO Unit`は、コマンドライン引数を読めず、常に終了コード{anchorTerm Names}`0`で成功を示すプログラムに対応する。
 * {anchorTerm Names}`main : IO UInt32`はCの{c}`int main(void)`に対応し、引数を取らず終了コードを返すプログラムのためのものであり、
 * {anchorTerm Names}`main : List String → IO UInt32`はCの{c}`int main(int argc, char **argv)`に対応し、引数を取り、成功か失敗を知らせるプログラムのためのものである。

引数が与えられなかった場合は、{anchorTerm main}`"-"`という引数一つで呼ばれたのと同じように、標準入力から読み込む。
そうでなければ、引数を順に処理する。
```module (anchor:=main)
def main (args : List String) : IO UInt32 :=
  match args with
  | [] => process 0 ["-"]
  | _ =>  process 0 args
```

# 動作を確かめる
%%%
tag := "example-cat-running"
%%%

:::paragraph
{lit}`feline`が動作するか確かめるには、まず{command feline2 "feline/2"}`lake build`でビルドする。
第一に、引数なしで呼び出したときは、標準入力から受け取ったものを出力するはずである。
次のコマンドが、
```command feline2 "feline/2" (shell := true)
echo "It works!" | lake exe feline
```
{commandOut feline2}`echo "It works!" | lake exe feline`を出力することを確かめる。
:::

:::paragraph
第二に、ファイルを引数として呼び出したときは、その内容を表示するはずである。
ファイル{lit}`test1.txt`の中身が
```plainFile "feline/2/test1.txt"
It's time to find a warm spot
```

であり、{lit}`test2.txt`の中身が
```plainFile "feline/2/test2.txt"
and curl up!
```

であるとき、次のコマンドは、

{command feline2 "feline/2" "lake exe feline test1.txt test2.txt"}

次を出力するはずである。
```commandOut feline2 "lake exe feline test1.txt test2.txt"
It's time to find a warm spot
and curl up!
```
:::

最後に、{lit}`-`という引数も適切に扱われるはずである。
```command feline2 "feline/2" (shell := true)
echo "and purr" | lake exe feline test1.txt - test2.txt
```

次が得られるはずである。
```commandOut feline2 "echo \"and purr\" | lake exe feline test1.txt - test2.txt"
It's time to find a warm spot
and purr
and curl up!
```


# 練習問題
%%%
tag := "example-cat-exercise"
%%%

{lit}`feline`に、使い方の情報を表示する機能を追加せよ。
拡張した版は、コマンドライン引数{lit}`--help`を受け付け、使えるコマンドラインオプションの説明を標準出力に書き出すようにする。
