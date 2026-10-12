module
public import VersoManual
import FPLean.Examples


open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"

set_option verso.exampleModule "HelloName"

example_module Hello

#doc (Manual) "Running a Program" =>
%%%
tag := "running-a-program"
%%%

:::paragraph
Leanのプログラムを動かす最も簡単な方法は、Leanの実行ファイルの{lit}`--run`オプションを使うことである。
{lit}`Hello.lean`というファイルを作り、次の内容を書く。

```module (module:=Hello)
def main : IO Unit := IO.println "Hello, world!"
```
:::

:::paragraph
次に、コマンドラインから次を実行する。

{command hello "simple-hello" "lean --run Hello.lean"}

プログラムは{commandOut hello}`lean --run Hello.lean`と表示して終了する。
:::



# 挨拶プログラムの解剖
%%%
tag := "hello-world-parts"
%%%

Leanを{lit}`--run`オプション付きで起動すると、プログラムの{lit}`main`の定義が呼び出される。
コマンドライン引数を取らないプログラムでは、{moduleName (module := Hello)}`main`の型は{moduleTerm}`IO Unit`とする。
つまり、{moduleName (module := Hello)}`main`は関数ではない。その型に矢印（{lit}`→`）がないためである。
{moduleTerm}`main`は副作用を持つ関数ではなく、実行すべき副作用の記述である。

{ref "polymorphism"}[前の章]で述べたように、{moduleTerm}`Unit`は最も単純な帰納型である。
引数を取らない{moduleTerm}`unit`というコンストラクタを一つだけ持つ。
Cの流れをくむ言語には、値を一切返さない{CSharp}`void`関数という考え方がある。
Leanでは、すべての関数が引数を取り値を返す。意味のある引数や戻り値がないことは、代わりに{moduleTerm}`Unit`型を使うことで示す。
{moduleTerm}`Bool`が1ビットの情報を表すなら、{moduleTerm}`Unit`は0ビットの情報を表す。

{moduleTerm}`IO α`は、実行すると例外を投げるか{moduleTerm}`α`型の値を返すプログラムの型である。
実行中、このプログラムは副作用を起こしうる。
このようなプログラムを{moduleTerm}`IO`*アクション*と呼ぶ。
Leanは、式の*評価*と{anchorTerm sig}`IO`アクションの*実行*を区別する。評価は、変数を値で置き換え、部分式を副作用なしに簡約するという数学的モデルに厳密に従う。実行は、外界とやり取りするために外部のシステムに頼る。
{moduleTerm}`IO.println`は、文字列から{moduleTerm}`IO`アクションへの関数である。実行すると、与えられた文字列を標準出力に書き込む。
このアクションは文字列を出力する際に環境から意味のある情報を読み取らないので、{moduleTerm}`IO.println`の型は{moduleTerm}`String → IO Unit`である。
もし意味のあるものを返すなら、その{moduleTerm}`IO`アクションの型が{moduleTerm}`Unit`以外になることで示される。



# 関数型プログラミングと副作用
%%%
tag := "fp-effects"
%%%

Leanの計算モデルは数式の評価に基づいており、変数にはちょうど一つの値が与えられ、その値は時間とともに変わらない。
式の評価結果は変わらず、同じ式をもう一度評価しても常に同じ結果になる。

一方で、役に立つプログラムは外界とやり取りしなければならない。
入力も出力もしないプログラムは、利用者にデータを尋ねることも、ディスクにファイルを作ることも、ネットワーク接続を開くこともできない。
LeanはLean自身で書かれており、Leanコンパイラはもちろんファイルを読み、ファイルを作り、テキストエディタとやり取りしている。
同じ式が常に同じ結果になる言語で、内容が時間とともに変わりうるディスク上のファイルを読むプログラムを、どうやって支えるのか。

この一見した矛盾は、副作用について少し違う見方をすると解消する。
コーヒーとサンドイッチを売る喫茶店を想像してほしい。
この店には従業員が二人いる。注文をさばく調理担当と、客とやり取りして注文票を出すカウンター担当である。
調理担当は無愛想な人物で、外の世界と関わりたくないと思っているが、この店の看板である食事と飲み物を安定して出すことにかけては非常に腕がよい。
ただしそのためには静けさが必要で、話しかけられて邪魔されるのを嫌う。
カウンター担当は人当たりがよいが、厨房のことはまったく分からない。
客はカウンター担当とやり取りし、実際の調理はすべて調理担当に任せる。
調理担当が客に確認したいこと（アレルギーの有無など）があれば、カウンター担当に短いメモを渡す。カウンター担当が客に聞き、結果をメモにして調理担当に返す。

このたとえでは、調理担当がLean言語である。
注文が入れば、調理担当は忠実に、いつも同じように、求められたものを出す。
カウンター担当は、外界とやり取りする実行時システムである。支払いを受け取り、料理を渡し、客と会話できる。
二人が協力すれば店の機能はすべて果たせるが、役割は分かれており、それぞれが得意な仕事を担う。
客を厨房に近づけないことで調理担当が本当に優れたコーヒーとサンドイッチ作りに集中できるのと同じように、Leanに副作用がないことで、プログラムを形式的な数学の証明の一部として使える。
また、部品どうしを結び付ける隠れた状態変化がないので、プログラマはプログラムの各部分を切り離して理解できる。
調理担当のメモは、Leanの式を評価して作られる{moduleTerm}`IO`アクションにあたる。カウンター担当の返事は、副作用から返ってくる値である。

この副作用のモデルは、Lean言語、そのコンパイラ、実行時システム（RTS）を合わせた全体の仕組みとよく似ている。
Cで書かれた実行時システムのプリミティブが、基本的な副作用をすべて実装している。
プログラムを実行すると、RTSが{moduleTerm}`main`アクションを呼び出し、それが新しい{moduleTerm}`IO`アクションをRTSに返して実行させる。
RTSはこれらのアクションを実行し、計算の実行は利用者のLeanコードに任せる。
Leanの内側から見れば、プログラムに副作用はなく、{moduleTerm}`IO`アクションは実行すべき作業の記述にすぎない。
プログラムの利用者から見れば、プログラムの中核の論理への入り口となる副作用の層がある。


# 現実の世界と関数型プログラミング
%%%
tag := "fp-world-passing"
%%%


Leanの副作用についてのもう一つの有用な見方は、{moduleTerm}`IO`アクションを、世界全体を引数に取り、値と新しい世界の組を返す関数とみなすものである。
この見方では、標準入力から1行読み取ることは*純粋な関数である*。毎回異なる世界が引数として渡されるからである。
標準出力に1行書き込むことも純粋な関数である。返される世界が、始めたときの世界とは異なるからである。
プログラムは、世界を使い回したり、新しい世界を返し忘れたりしないよう注意する必要がある。それは結局、時間旅行か世界の終わりになってしまうからである。
抽象化の境界を慎重に引けば、この書き方は安全にできる。
すべての原始的な{moduleTerm}`IO`アクションが世界を一つ受け取って新しい世界を返し、この不変条件を保つ道具でしか組み合わせられないなら、この問題は起こらない。

このモデルは実装できない。
宇宙全体をLeanの値にしてメモリに置くことなどできないからである。
しかし、世界を表す抽象的なトークンを使った、このモデルの変種なら実装できる。
プログラムが起動すると、世界のトークンが渡される。
そのトークンはIOのプリミティブに渡され、返ってきたトークンも同様に次の段階へ渡される。
プログラムの終わりに、トークンはオペレーティングシステムに返される。

この副作用のモデルは、RTSが実行する作業の記述としての{moduleTerm}`IO`アクションが、Leanの内部でどう表されているかをよく説明している。
実際の世界を変換する本当の関数は、抽象化の壁の向こうにある。
しかし実際のプログラムは、一つだけでなく一連の副作用から成るのが普通である。
複数の副作用を使うプログラムを書けるように、Leanには{kw}`do`記法という部分言語がある。これを使うと、原始的な{moduleTerm}`IO`アクションを安全に組み合わせて、より大きく役に立つプログラムにできる。

# {anchorName all}`IO`アクションの組み合わせ
%%%
tag := "combining-io-actions"
%%%

役に立つプログラムの多くは、出力だけでなく入力も受け取る。
さらに、入力に基づいて判断し、入力のデータを計算の一部に使うこともある。
次の{lit}`HelloName.lean`というプログラムは、利用者に名前を尋ねてから挨拶する。

```module (anchor:=all)
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropEndWhile Char.isWhitespace

  stdout.putStrLn s!"Hello, {name}!"
```

このプログラムでは、{anchorName all}`main`アクションは{kw}`do`ブロックから成る。
このブロックには*文*の並びが入っており、{kw}`let`で導入するローカル変数と、実行すべきアクションの両方を書ける。
SQLがデータベースとやり取りするための専用言語だと考えられるのと同じように、{kw}`do`記法は、命令的なプログラムを表すためにLeanの中に用意された専用の部分言語だと考えられる。
{kw}`do`ブロックで組み立てた{anchorName all}`IO`アクションは、文を順に実行することで実行される。

このプログラムも、前のプログラムと同じように実行できる。

{commandLine}`lean --run HelloName.lean`

利用者が{lit}`David`と答えた場合、プログラムとのやり取りは次のようになる。

```interaction helloName "hello-name" -showCommand
{ command := "lean", args := #["--run", "HelloName.lean"],
  script := #[
    .expect "How would you like to be addressed?",
    .send "David",
    .expect "Hello, David!",
    .exitCode 0] }
---
< How would you like to be addressed?
> David
< Hello, David!
```

型シグネチャの行は{lit}`Hello.lean`のものと同じである。
```module (anchor:=sig)
def main : IO Unit := do
```
唯一の違いは、末尾に{moduleTerm}`do`というキーワードが付き、これが一連のコマンドを始めることである。
{kw}`do`の後に続く、インデントされた各行が同じコマンドの並びに属する。

最初の二行は次のとおりで、
```module (anchor:=setup)
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
```

それぞれライブラリのアクション{moduleTerm (anchor := setup)}`IO.getStdin`と{moduleTerm (anchor := setup)}`IO.getStdout`を実行して、{moduleTerm (anchor := setup)}`stdin`と{moduleTerm (anchor := setup)}`stdout`のハンドルを取得する。
{moduleTerm}`do`ブロックの中では、{moduleTerm}`let`の意味が普通の式の中とは少し異なる。
通常、{moduleTerm}`let`のローカル定義を使えるのは、その定義の直後に続く一つの式だけである。
{moduleTerm}`do`ブロックでは、{moduleTerm}`let`で導入したローカル束縛を、直後の文だけでなく、そのブロックの残りすべての文で使える。
さらに、{moduleTerm}`let`は通常、定義する名前とその定義を{lit}`:=`で結ぶが、{moduleTerm}`do`の中の{moduleTerm}`let`束縛には左矢印（{lit}`←`または{lit}`<-`）を使うものもある。
矢印を使うと、その式の値は実行すべき{moduleTerm}`IO`アクションであるという意味になり、アクションの結果がローカル変数に保存される。
言い換えれば、矢印の右の式の型が{moduleTerm}`IO α`なら、{moduleTerm}`do`ブロックの残りでは変数の型が{moduleTerm}`α`になる。
{moduleTerm (anchor := setup)}`IO.getStdin`と{moduleTerm (anchor := setup)}`IO.getStdout`が{moduleTerm (anchor := sig)}`IO`アクションなのは、プログラムの中で{moduleTerm (anchor := setup)}`stdin`と{moduleTerm (anchor := setup)}`stdout`を局所的に差し替えられるようにするためである。これができると便利なことがある。
Cのように大域変数だと差し替える意味のある方法がないが、{moduleName}`IO`アクションは実行するたびに異なる値を返せる。

{moduleTerm}`do`ブロックの次の部分は、利用者に名前を尋ねる役割を担う。

```module (anchor:=question)
  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropEndWhile Char.isWhitespace
```

最初の行が質問を{moduleTerm (anchor := setup)}`stdout`に書き、二番目の行が{moduleTerm (anchor := setup)}`stdin`から入力を受け取り、三番目の行が入力行の末尾の改行（および他の末尾の空白）を取り除く。
{moduleTerm (anchor := question)}`name`の定義で{lit}`←`ではなく{lit}`:=`を使っているのは、{moduleTerm}`String.dropEndWhile`が{moduleTerm (anchor := sig)}`IO`アクションではなく、文字列に対する普通の関数だからである。

最後に、プログラムの最終行は次のとおりである。
```module (anchor:=answer)
  stdout.putStrLn s!"Hello, {name}!"
```

{ref "string-interpolation"}[文字列補間]を使って、渡された名前を挨拶の文字列に埋め込み、その結果を{moduleTerm (anchor := setup)}`stdout`に書き込む。
