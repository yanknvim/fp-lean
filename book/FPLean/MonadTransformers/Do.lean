module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.MonadTransformers.Do"


#doc (Manual) "More do Features" =>
%%%
tag := "more-do-features"
%%%

Leanの{kw}`do`記法は、命令型プログラミング言語に似た、モナドを使うプログラムを書くための構文を与える。
{kw}`do`記法は、モナドを使うプログラムの便利な構文を与えるだけでなく、ある種のモナド変換子を使うための構文も与える。

# 枝が一つの{kw}`if`
%%%
tag := "single-branched-if"
%%%

モナドを扱うときによくあるパターンは、ある条件が真のときにだけ副作用を行うことである。
たとえば{anchorName countLettersModify (module := Examples.MonadTransformers.Defs)}`countLetters`には母音か子音かの検査があり、どちらでもない文字は状態に影響しない。
これは、{kw}`else`の枝を副作用のない{anchorTerm countLettersModify (module := Examples.MonadTransformers.Defs)}`pure ()`に評価させることで表している。

```anchor countLettersModify (module := Examples.MonadTransformers.Defs)
def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        else -- modified or non-English letter
          pure ()
      else throw (.notALetter c)
      loop cs
  loop str.toList
```

{kw}`if`が式ではなく{kw}`do`ブロックの中の文であるときは、{anchorTerm countLettersModify (module:=Examples.MonadTransformers.Defs)}`else pure ()`を単に省け、Leanが自動で挿入する。
次の{anchorName countLettersNoElse}`countLetters`の定義はまったく等価である。

```anchor countLettersNoElse
def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
      else throw (.notALetter c)
      loop cs
  loop str.toList
```
状態モナドを使って、リストの中でモナドの検査を満たす要素を数えるプログラムは次のように書ける。

```anchor count
def count [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | [] => pure ()
  | x :: xs => do
    if ← p x then
      modify (· + 1)
    count p xs
```

同様に、{lit}`if not E1 then STMT...`は{lit}`unless E1 do STMT...`とも書ける。
モナドの検査を満たさない要素を数える、{anchorName count}`count`の逆のものは、{kw}`if`を{kw}`unless`に置き換えれば書ける。

```anchor countNot
def countNot [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | [] => pure ()
  | x :: xs => do
    unless ← p x do
      modify (· + 1)
    countNot p xs
```

枝が一つの{kw}`if`と{kw}`unless`を理解するのに、モナド変換子を考える必要はない。
これらは、欠けている枝を{anchorTerm count}`pure ()`で置き換えるだけである。
しかし、この節の残りの拡張は、Leanが{kw}`do`ブロックを自動で書き換え、その{kw}`do`ブロックを書いているモナドの上に局所的な変換子を加えることを要する。

# 早期リターン
%%%
tag := "early-return"
%%%

標準ライブラリには、リストの中で検査を満たす最初の要素を返す{anchorName findHuh}`List.find?`関数がある。
{anchorName findHuh}`Option`がモナドであることを使わない単純な実装は、再帰関数でリストをたどり、目的の要素が見つかったときに{kw}`if`でループを止める。

```anchor findHuhSimple
def List.find? (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs =>
    if p x then
      some x
    else
      find? p xs
```

命令型言語には通常、関数の実行を中断して呼び出し側に値をすぐ返す{kw}`return`キーワードがある。
Leanではこれが{kw}`do`記法で使え、{kw}`return`は{kw}`do`ブロックの実行を止め、{kw}`return`の引数がそのモナドから返される値になる。
言い換えれば、{anchorName findHuhFancy}`List.find?`は次のように書けた。

```anchor findHuhFancy
def List.find? (p : α → Bool) : List α → Option α
  | [] => failure
  | x :: xs => do
    if p x then return x
    find? p xs
```

命令型言語の早期リターンは、現在のスタックフレームだけを巻き戻せる例外に少し似ている。
早期リターンも例外も、コードのまとまりの実行を終わらせ、事実上周囲のコードを投げられた値で置き換える。
裏では、Leanの早期リターンは{anchorName runCatch}`ExceptT`の一種で実装されている。
早期リターンを使う{kw}`do`ブロックはそれぞれ、例外の処理役（{anchorName MonadExcept (module:=Examples.MonadTransformers.Defs)}`tryCatch`関数の意味での）で包まれる。
早期リターンは、その値を例外として投げることに変換され、処理役が投げられた値を受け取ってすぐに返す。
言い換えれば、その{kw}`do`ブロックの元の戻り値の型が例外の型としても使われる。

これをより具体的にすると、補助関数{anchorName runCatch}`runCatch`は、例外の型と戻り値の型が同じときに、モナド変換子の積み重ねの一番上から{anchorName runCatch}`ExceptT`の層を一枚はがす。

```anchor runCatch
def runCatch [Monad m] (action : ExceptT α m α) : m α := do
  match ← action with
  | Except.ok x => pure x
  | Except.error x => pure x
```
{anchorName findHuh}`List.find?`の早期リターンを使う{kw}`do`ブロックは、{anchorName desugaredFindHuh}`runCatch`の使用で包み、早期リターンを{anchorName desugaredFindHuh}`throw`に置き換えることで、早期リターンを使わない{kw}`do`ブロックに変換される。

```anchor desugaredFindHuh
def List.find? (p : α → Bool) : List α → Option α
  | [] => failure
  | x :: xs =>
    runCatch do
      if p x then throw x else pure ()
      monadLift (find? p xs)
```

早期リターンが役に立つもう一つの場面は、引数や入力が正しくなければ早期に終了するコマンドラインアプリケーションである。
多くのプログラムは、本体に進む前に引数と入力を検査する部分から始まる。
次の版の{ref "running-a-program"}[あいさつのプログラム{lit}`hello-name`]は、コマンドライン引数が与えられていないことを調べる。
```anchor main (module := EarlyReturn)
def main (argv : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr

  unless argv == [] do
    stderr.putStrLn s!"Expected no arguments, but got {argv.length}"
    return 1

  stdout.putStrLn "How would you like to be addressed?"
  stdout.flush

  let name := (← stdin.getLine).trimAscii
  if name.isEmpty then
    stderr.putStrLn s!"No name provided"
    return 1

  stdout.putStrLn s!"Hello, {name}!"

  return 0
```
引数なしで実行し、名前として{lit}`David`を入力すると、前の版と同じ結果になる。
```interaction «early-return» "early-return"
{ command := "lean", args := #["--run", "EarlyReturn.lean"],
  script := #[
    .expect "How would you like to be addressed?",
    .send "David",
    .expect "Hello, David!",
    .exitCode 0] }
---
$ lean --run EarlyReturn.lean
< How would you like to be addressed?
> David
< Hello, David!
```

名前を答えとしてではなくコマンドライン引数として与えるとエラーになる。
```interaction «early-return» "early-return"
{ command := "lean", args := #["--run", "EarlyReturn.lean", "David"],
  script := #[
    .expect "Expected no arguments, but got 1",
    .exitCode 1] }
---
$ lean --run EarlyReturn.lean David
< Expected no arguments, but got 1
```

また、名前を与えないと別のエラーになる。
```interaction «early-return» "early-return"
{ command := "lean", args := #["--run", "EarlyReturn.lean"],
  script := #[
    .expect "How would you like to be addressed?",
    .send "",
    .expect "No name provided",
    .exitCode 1] }
---
$ lean --run EarlyReturn.lean
< How would you like to be addressed?
>
< No name provided
```

早期リターンを使うプログラムは、早期リターンを使わない次の版のように制御の流れを入れ子にする必要を避けられる。
```anchor nestedmain (module := EarlyReturn)
def main (argv : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr

  if argv != [] then
    stderr.putStrLn s!"Expected no arguments, but got {argv.length}"
    pure 1
  else
    stdout.putStrLn "How would you like to be addressed?"
    stdout.flush

    let name := (← stdin.getLine).trimAscii
    if name.isEmpty then
      stderr.putStrLn s!"No name provided"
      pure 1
    else
      stdout.putStrLn s!"Hello, {name}!"
      pure 0
```

Leanの早期リターンと命令型言語の早期リターンの重要な違いの一つは、Leanの早期リターンが現在の{kw}`do`ブロックにしか効かないことである。
関数の定義全体が同じ{kw}`do`ブロックにあるときは、この違いは問題にならない。
しかし{kw}`do`が他の構造の下にあると、この違いがはっきり現れる。
たとえば、次の{anchorName greet}`greet`の定義を考える。

```anchor greet
def greet (name : String) : String :=
  "Hello, " ++ Id.run do return name
```
式{anchorTerm greetDavid}`greet "David"`は{anchorTerm greetDavid}`"David"`ではなく{anchorTerm greetDavid}`"Hello, David"`に評価される。

# ループ
%%%
tag := "loops"
%%%

可変状態を持つどのプログラムも状態を引数として渡すプログラムに書き換えられるのと同じように、どのループも再帰関数に書き換えられる。
ある観点では、{anchorName findHuh}`List.find?`は再帰関数として書くのが最も明快である。
何しろ、その定義はリストの構造を写している。先頭が検査を通ればそれを返すべきであり、そうでなければ残りを探す。
もう要素が残っていなければ、答えは{anchorName findHuhSimple}`none`である。
別の観点では、{anchorName findHuh}`List.find?`はループとして書くのが最も明快である。
何しろ、このプログラムは満足のいく要素が見つかるまで順に要素を調べ、見つかった時点で終わる。
ループが何も返さずに終われば、答えは{anchorName findHuhSimple}`none`である。

## ForMによるループ
%%%
tag := "looping-with-forM"
%%%

Leanには、容器の型をループすることを記述する型クラスがある。
このクラスは{anchorName ForM}`ForM`という。

```anchor ForM
class ForM (m : Type u → Type v) (γ : Type w₁)
    (α : outParam (Type w₂)) where
  forM (coll : γ) (f : α → m PUnit) : m PUnit
```
このクラスはかなり一般的である。
引数{anchorName ForM}`m`は望む副作用を可能にするもので通常はモナドであり、{anchorName ForM}`γ`はループする対象のコレクション、{anchorName ForM}`α`はそのコレクションの要素の型である。
通常{anchorName ForM}`m`はどのモナドでもよいが、たとえば{anchorName printArray}`IO`でのループしか支えないデータ構造もありうる。
{anchorName ForM}`forM`メソッドはコレクションと、そのコレクションの各要素に対して副作用のために実行する動作を取り、その動作の実行を引き受ける。

{anchorName ListForM}`List`のインスタンスは{anchorName ListForM}`m`をどのモナドでもよいとし、{anchorName ForM}`γ`を{anchorTerm ListForM}`List α`に、クラスの{anchorName ForM}`α`をリストにあるのと同じ{anchorName ListForM}`α`にする。

```anchor ListForM
def List.forM [Monad m] : List α → (α → m PUnit) → m PUnit
  | [], _ => pure ()
  | x :: xs, action => do
    action x
    forM xs action

instance [Monad m] : ForM m (List α) α where
  forM := List.forM
```
{ref "reader-io-implementation"}[{lit}`doug`の{anchorName doList (module := DirTree)}`doList`関数]は、リストに対する{anchorName ForM}`forM`である。
{anchorName ForM}`forM`を使うと{anchorName countLettersForM}`countLetters`をずっと短くできる。

```anchor countLettersForM
def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  forM str.toList fun c => do
    if c.isAlpha then
      if vowels.contains c then
        modify fun st => {st with vowels := st.vowels + 1}
      else if consonants.contains c then
        modify fun st => {st with consonants := st.consonants + 1}
    else throw (.notALetter c)
```


{anchorName ManyForM}`Many`のインスタンスもよく似ている。

```anchor ManyForM
def Many.forM [Monad m] : Many α → (α → m PUnit) → m PUnit
  | Many.none, _ => pure ()
  | Many.more first rest, action => do
    action first
    forM (rest ()) action

instance [Monad m] : ForM m (Many α) α where
  forM := Many.forM
```

{anchorName ForM}`γ`はどの型でもよいので、{anchorName ForM}`ForM`は多相でないコレクションも支えられる。
とても単純なコレクションとして、ある与えられた数より小さい自然数を逆順に並べたものがある。

```anchor AllLessThan
structure AllLessThan where
  num : Nat
```
その{anchorName ForM}`ForM`演算子は、与えられた動作をより小さい各{anchorName ListCount}`Nat`に適用する。

```anchor AllLessThanForM
def AllLessThan.forM [Monad m]
    (coll : AllLessThan) (action : Nat → m Unit) :
    m Unit :=
  let rec countdown : Nat → m Unit
    | 0 => pure ()
    | n + 1 => do
      action n
      countdown n
  countdown coll.num

instance [Monad m] : ForM m AllLessThan Nat where
  forM := AllLessThan.forM
```
5より小さい各数に{anchorName AllLessThanForMRun}`IO.println`を実行するのは、{anchorName ForM}`ForM`で行える。
```anchor AllLessThanForMRun
#eval forM { num := 5 : AllLessThan } IO.println
```
```anchorInfo AllLessThanForMRun
4
3
2
1
0
```

特定のモナドでしか働かない{anchorName ForM}`ForM`インスタンスの例として、標準入力のようなIOストリームから読んだ行をループするものがある。
```anchor LinesOf (module := ForMIO)
structure LinesOf where
  stream : IO.FS.Stream

partial def LinesOf.forM
    (readFrom : LinesOf) (action : String → IO Unit) :
    IO Unit := do
  let line ← readFrom.stream.getLine
  if line == "" then return ()
  action line
  forM readFrom action

instance : ForM IO LinesOf String where
  forM := LinesOf.forM
```
{anchorName LinesOf (module := ForMIO)}`LinesOf.forM`の定義が{kw}`partial`と印を付けられているのは、そのストリームが有限である保証がないためである。
この場合、{anchorName names}`IO.FS.Stream.getLine`は{anchorName countToThree}`IO`モナドでしか働かないので、ループに他のモナドは使えない。

この例のプログラムは、このループの仕組みを使って、文字を含まない行を除く。
```anchor main (module := ForMIO)
def main (argv : List String) : IO UInt32 := do
  if argv != [] then
    IO.eprintln "Unexpected arguments"
    return 1

  forM (LinesOf.mk (← IO.getStdin)) fun line => do
    if line.any (·.isAlpha) then
      IO.print line

  return 0
```
```commands formio "formio" (show := false)
$ ls
expected
test-data
$ cp ../ForMIO.lean .
$ ls
ForMIO.lean
expected
test-data
```
ファイル{lit}`test-data`の中身は次のとおりである。
```file formio "formio/test-data"
Hello!
!!!!!
12345
abc123

Ok
```
{lit}`ForMIO.lean`に入っているこのプログラムを起動すると、次の出力になる。
```commands formio "formio"
$ lean --run ForMIO.lean < test-data
Hello!
abc123
Ok
```

## 繰り返しを止める
%%%
tag := "break"
%%%

ループを早期に終わらせるのは{anchorName ForM}`ForM`では難しい。
{anchorName AllLessThan}`AllLessThan`にある{anchorName AllLessThan}`Nat`を{anchorTerm OptionTcountToThree}`3`に達するまでだけ繰り返す関数を書くには、途中でループを止める手段が要る。
これを実現する一つの方法は、{anchorName ForM}`ForM`を{anchorName OptionTExec}`OptionT`モナド変換子と組み合わせて使うことである。
まず{anchorName OptionTExec}`OptionT.exec`を定義する。これは戻り値と、変換後の計算が成功したかどうかの両方の情報を捨てる。

```anchor OptionTExec
def OptionT.exec [Applicative m] (action : OptionT m α) : m Unit :=
  action *> pure ()
```
そして、{anchorName OptionTExec}`OptionT`の{anchorName AlternativeOptionT (module:=Examples.MonadTransformers.Defs)}`Alternative`インスタンスでのfailureを使えば、ループを早期に終わらせられる。

```anchor OptionTcountToThree
def countToThree (n : Nat) : IO Unit :=
  let nums : AllLessThan := ⟨n⟩
  OptionT.exec (forM nums fun i => do
    if i < 3 then failure else IO.println i)
```
簡単な試験で、この解決策が働くことが分かる。
```anchor optionTCountSeven
#eval countToThree 7
```
```anchorInfo optionTCountSeven
6
5
4
3
```

しかし、このコードはあまり読みやすくない。
ループを早期に終わらせるのはよくある作業なので、Leanはそれを容易にする糖衣構文をさらに用意している。
同じ関数は次のようにも書ける。

```anchor countToThree
def countToThree (n : Nat) : IO Unit := do
  let nums : AllLessThan := ⟨n⟩
  for i in nums do
    if i < 3 then break
    IO.println i
```
試すと、前の版とまったく同じように働くことが分かる。
```anchor countSevenFor
#eval countToThree 7
```
```anchorInfo countSevenFor
6
5
4
3
```

:::paragraph
{kw}`for`{lit}` ...`{kw}`in`{lit}` ...`{kw}`do`{lit}` ...`構文は{anchorName ForInIOAllLessThan}`ForIn`という型クラスの使用に脱糖される。これは{anchorName ForM}`ForM`のやや複雑な版で、状態と早期の終了を追跡する。
標準ライブラリには、{anchorName ForM}`ForM`インスタンスを{anchorName ForInIOAllLessThan}`ForIn`インスタンスに変換する{anchorName ForInIOAllLessThan}`ForM.forIn`という適合器がある。
この適合器は内部で{anchorName countLettersForM}`StateT`と{anchorName runCatch}`ExceptT`を使うので、{anchorName ForM}`ForM`インスタンスが、特定の一つのモナドだけでなく、モナド変換子から組み立てたモナドでも使えることを要求する。
{anchorName ForM}`ForM`インスタンスに基づく{kw}`for`ループを使えるようにするには、{anchorName AllLessThan}`AllLessThan`と{anchorName AllLessThan}`Nat`を適切に置き換えて、次のようなものを加える。
```anchor ForInIOAllLessThan
instance [Monad m] : ForIn m AllLessThan Nat where
  forIn := ForM.forIn
```
:::

{kw}`for`ループでも早期リターンが使える。
早期リターンを含む{kw}`do`ブロックを例外モナド変換子の使用へ変換するやり方は、{anchorName ForM}`ForM`の下でも、先ほどの{anchorName OptionTExec}`OptionT`で繰り返しを止めるやり方と同じように当てはまる。
この版の{anchorName findHuh}`List.find?`はその両方を使う。

```anchor findHuh
def List.find? (p : α → Bool) (xs : List α) : Option α := do
  for x in xs do
    if p x then return x
  failure
```

{kw}`break`に加えて、{kw}`for`ループは{kw}`continue`を支え、ある繰り返しでループ本体の残りを飛ばせる。
別の（しかし紛らわしい）{anchorName findHuhCont}`List.find?`の書き方は、検査を満たさない要素を飛ばす。

```anchor findHuhCont
def List.find? (p : α → Bool) (xs : List α) : Option α := do
  for x in xs do
    if not (p x) then continue
    return x
  failure
```

{deftech}*範囲*は、ある型の連続した要素の並びを、下界から上界まで表す。
界は*開*でもよく、その場合はその界は範囲に含まれず、*閉*でもよく、その場合は含まれる。
範囲は非有界でもよく、無限に続くか、その型の最小値か最大値に達するまで続く。

:::paragraph
範囲は、その界を記述する命名規則を持つ型の集まりで表される。
各型の名前は{lit}`R`で始まり、続く二文字がそれぞれ下界と上界を決める。

* {lit}`o`は開いた界を表し、その界の値は含まれない。
* {lit}`c`は閉じた界を表し、その界の値が含まれる。
* {lit}`i`は無限の界を表し、その範囲を制限しない。

たとえば、型{anchorTerm names}`Std.Rco Nat`は{anchorName names}`Nat`の左閉右開の並びを表し、下界を含むが上界は省く。また{anchorTerm names}`Std.Roi Nat`は{anchorName names}`Nat`の無限の並びを表し、下界のすぐ上から始まる。
無限の界がいつも無限の範囲になるわけではない。たとえば{anchorTerm names}`Std.Rio Nat`には下界がないが、{anchorName names}`Nat`自体が{anchorTerm names}`0`という本来の下界を持つので、その並びは有限である。
:::

Leanには範囲を作る特別な構文があり、それぞれの界を指定できる。
範囲は界の間に三点を置いて指定し、界自体は具体的な値か、非有界の範囲を表すアスタリスクで指定できる。
たとえば{anchorTerm ranges}`3`から{anchorTerm ranges}`10`までの範囲は{anchorTerm ranges}`3...10`と書き、型は{anchorTerm ranges}`Std.Rco Nat`である。
既定では、範囲は左閉右開である。
つまり{anchorTerm ranges}`3...10`は{anchorTerm ranges}`3`を含むが{anchorTerm ranges}`10`は含まない。
この既定は上書きできる。{lit}`<`で開いた上界か下界を指定でき、{lit}`=`で閉じた上界を指定できる。
{anchorTerm ranges}`3<...=10`は{anchorTerm ranges}`3`を含まないが{anchorTerm ranges}`10`は含み、{anchorTerm ranges}`3...=10`は両方を含み、{anchorTerm ranges}`3<...10`はどちらも含まない。
{anchorTerm ranges}`3<...=10`の型は{anchorTerm ranges}`Std.Roc Nat`、{anchorTerm ranges}`3<...10`の型は{anchorTerm ranges}`Std.Roo Nat`である。
範囲{anchorTerm ranges}`*...5`には{anchorTerm ranges}`0`、{anchorTerm ranges}`1`、{anchorTerm ranges}`2`、{anchorTerm ranges}`3`、{anchorTerm ranges}`4`が入り、{anchorTerm ranges}`3...*`には{anchorTerm ranges}`3`以上の自然数がすべて入る。

範囲は常に昇順である。
範囲の下界が上界より大きい場合、逆順に進むのではなく、どの値も含まない。
たとえば{anchorTerm ranges}`10...3`は空である。

:::paragraph
適切な型クラスのインスタンスがあれば、範囲を{kw}`for`ループと組み合わせて範囲から値を取り出せる。
このプログラムは4から8までの偶数を表示する。
```anchor fourToEight
def fourToEight : IO Unit := do
  for i in 2...5 do
    IO.println (i * 2)
```
実行すると次のようになる。
```anchorInfo fourToEightOut
4
6
8
```
これは{anchorTerm showLetters}`'l'`から{anchorTerm showLetters}`'p'`までの文字を表示する。
```anchor showLetters
#eval do
  for letter in 'l'...='p' do
    IO.println letter
```
```anchorInfo showLetters
l
m
n
o
p
```
:::


最後に、{kw}`for`ループは{kw}`in`の句をコンマで区切ることで、複数のコレクションを並行に繰り返せる。
繰り返しは最初のコレクションの要素が尽きたときに止まる。したがって次の宣言は、

```anchor parallelLoop
def parallelLoop := do
  for x in ["currant", "gooseberry", "rowan"], y in 'a'...'e' do
    IO.println (x, y)
```
三行の出力になる。
```anchor parallelLoopOut
#eval parallelLoop
```
```anchorInfo parallelLoopOut
(currant, a)
(gooseberry, b)
(rowan, c)
```

多くのデータ構造は、その要素がそのコレクションから取り出されたという証拠をループ本体に加える、{anchorName ForInIOAllLessThan}`ForIn`型クラスの強化版を実装している。
これらは、要素の名前の前に証拠の名前を与えることで使える。
この関数は配列の要素を添字とともにすべて表示し、コンパイラは証拠{anchorName printArray}`h`のおかげで配列の参照がすべて安全であると判断できる。

```anchor printArray
def printArray [ToString α] (xs : Array α) : IO Unit := do
  for h : i in 0...xs.size do
    IO.println s!"{i}:\t{xs[i]}"
```
この例で{anchorName printArray}`h`は{anchorTerm printArrayEv}`i ∈ 0...xs.size`の証拠であり、{anchorTerm printArrayEv}`xs[i]`が安全かを調べるタクティクはこれを{anchorTerm printArrayEv}`i < xs.size`の証拠に変換できる。

# 可変変数
%%%
tag := "let-mut"
%%%

早期の{kw}`return`、{kw}`else`のない{kw}`if`、{kw}`for`ループに加えて、Leanは{kw}`do`ブロックの中での局所的な可変変数を支える。
裏では、これらの可変変数は真の可変変数で実装されるのではなく、{anchorName twoStateT}`StateT`に相当するコードに脱糖される。
ここでもまた、関数型プログラミングで命令型プログラミングをまねている。

局所的な可変変数は、普通の{kw}`let`ではなく{kw}`let mut`で導入する。
{anchorName two}`two`の定義は、副作用を導入せずに{kw}`do`構文を使えるように恒等モナド{anchorName sameBlock}`Id`を使い、{anchorTerm two_spec}`2`まで数える。

```anchor two
def two : Nat := Id.run do
  let mut x := 0
  x := x + 1
  x := x + 1
  return x
```
このコードは、{anchorName twoStateT}`StateT`を使って{anchorTerm twoStateT}`1`を二度足す定義と等価である。

```anchor twoStateT
def two : Nat :=
  let block : StateT Nat Id Nat := do
    modify (· + 1)
    modify (· + 1)
    return (← get)
  let (result, _finalState) := block 0
  result
```

局所的な可変変数は、モナド変換子の便利な構文を与える{kw}`do`記法の他の機能すべてとよく合う。
{anchorName three}`three`の定義は、要素が三つのリストの要素の数を数える。

```anchor three
def three : Nat := Id.run do
  let mut x := 0
  for _ in [1, 2, 3] do
    x := x + 1
  return x
```
同様に、{anchorName six}`six`はリストの要素を足す。

```anchor six
def six : Nat := Id.run do
  let mut x := 0
  for y in [1, 2, 3] do
    x := x + y
  return x
```

{anchorName ListCount}`List.count`は、リストの中で検査を満たす要素の数を数える。

```anchor ListCount
def List.count (p : α → Bool) (xs : List α) : Nat := Id.run do
  let mut found := 0
  for x in xs do
    if p x then found := found + 1
  return found
```

局所的な可変変数は、{anchorName twoStateT}`StateT`を局所的に明示して使うより便利で読みやすいことがある。
しかし、命令型言語の制限のない可変変数の力はない。
特に、導入した{kw}`do`ブロックの中でしか変更できない。
つまりたとえば、{kw}`for`ループを、それ以外は等価な再帰の補助関数で置き換えることはできない。
この版の{anchorName nonLocalMut}`List.count`は、
```anchor nonLocalMut
def List.count (p : α → Bool) (xs : List α) : Nat := Id.run do
  let mut found := 0
  let rec go : List α → Id Unit
    | [] => pure ()
    | y :: ys => do
      if p y then found := found + 1
      go ys
  return found
```
{anchorName nonLocalMut}`found`を変更しようとすると次のエラーになる。
```anchorError nonLocalMut
Variable `found` cannot be mutated. Only variables declared using `let mut` can be mutated.
      If you did not intend to mutate but define `found`, consider using `let found` instead
```
これは、その再帰関数が恒等モナドで書かれており、{anchorName twoStateT}`StateT`で変換されるのは、その変数を導入した{kw}`do`ブロックのモナドだけだからである。

# 何が{kw}`do`ブロックと見なされるか
%%%
tag := "do-block-boundaries"
%%%

{kw}`do`記法の多くの機能は、一つの{kw}`do`ブロックにしか当てはまらない。
早期リターンは現在のブロックを終わらせ、可変変数は定義されたブロックの中でしか変更できない。
これらを有効に使うには、何が「同じブロック」と見なされるかを知ることが重要である。

一般には、{kw}`do`キーワードに続く字下げされたブロックが一つのブロックと見なされ、そのすぐ下に続く文の並びがそのブロックの一部である。
あるブロックに含まれてはいても独立したブロックにある文は、そのブロックの一部とは見なされない。
しかし、何が正確に同じブロックと見なされるかを定める規則はやや細かいので、いくつか例を示す。
規則の正確な姿は、可変変数を持つプログラムを用意し、どこで変更が許されるかを見れば試せる。
このプログラムには、可変変数と同じブロックにあることが明らかな変更がある。

```anchor sameBlock
example : Id Unit := do
  let mut x := 0
  x := x + 1
```

{lit}`:=`で名前を定義する{kw}`let`文の一部である{kw}`do`ブロックで変更が起きる場合、それはそのブロックの一部とは見なされない。
```anchor letBodyNotBlock
example : Id Unit := do
  let mut x := 0
  let other := do
    x := x + 1
  other
```
```anchorError letBodyNotBlock
Variable `x` cannot be mutated. Only variables declared using `let mut` can be mutated.
      If you did not intend to mutate but define `x`, consider using `let x` instead
```
しかし、{lit}`←`で名前を定義する{kw}`let`文の下にある{kw}`do`ブロックは、周囲のブロックの一部と見なされる。
次のプログラムは受け付けられる。

```anchor letBodyArrBlock
example : Id Unit := do
  let mut x := 0
  let other ← do
    x := x + 1
  pure other
```

同様に、関数の引数として現れる{kw}`do`ブロックは、周囲のブロックから独立している。
次のプログラムは受け付けられない。
```anchor funArgNotBlock
example : Id Unit := do
  let mut x := 0
  let addFour (y : Id Nat) := Id.run y + 4
  addFour do
    x := 5
```
```anchorError funArgNotBlock
Variable `x` cannot be mutated. Only variables declared using `let mut` can be mutated.
      If you did not intend to mutate but define `x`, consider using `let x` instead
```

{kw}`do`キーワードがまったく冗長なら、新しいブロックを導入しない。
このプログラムは受け付けられ、この節の最初のものと等価である。

```anchor collapsedBlock
example : Id Unit := do
  let mut x := 0
  do x := x + 1
```

{kw}`do`の下の枝（{kw}`match`や{kw}`if`が導入するものなど）の中身は、冗長な{kw}`do`を加えても加えなくても、周囲のブロックの一部と見なされる。
次のプログラムはすべて受け付けられる。

```anchor ifDoSame
example : Id Unit := do
  let mut x := 0
  if x > 2 then
    x := x + 1
```

```anchor ifDoDoSame
example : Id Unit := do
  let mut x := 0
  if x > 2 then do
    x := x + 1
```

```anchor matchDoSame
example : Id Unit := do
  let mut x := 0
  match true with
  | true => x := x + 1
  | false => x := 17
```

```anchor matchDoDoSame
example : Id Unit := do
  let mut x := 0
  match true with
  | true => do
    x := x + 1
  | false => do
    x := 17
```
同様に、{kw}`for`と{kw}`unless`の構文の一部として現れる{kw}`do`は、その構文の一部にすぎず、新しい{kw}`do`ブロックを導入しない。
これらのプログラムも受け付けられる。

```anchor doForSame
example : Id Unit := do
  let mut x := 0
  for y in 1...5 do
   x := x + y
```

```anchor doUnlessSame
example : Id Unit := do
  let mut x := 0
  unless 1 < 5 do
    x := x + 1
```


# 命令型か関数型か
%%%
tag := none
%%%

Leanの{kw}`do`記法が与える命令型の機能により、多くのプログラムがRust、Java、C#のような言語の対応するものと非常によく似たものになる。
この類似は、命令型のアルゴリズムをLeanに移すときに非常に便利であり、命令型で考えるのが最も自然な作業もある。
モナドとモナド変換子の導入により、命令型のプログラムを純粋な関数型言語で書けるようになり、モナド（局所的に変換されたものでもよい）のための専用の構文としての{kw}`do`記法は、関数型プログラマに両方の利点を与える。不変性がもたらす強力な推論の原理と、型システムによる使える副作用の厳密な制御が、副作用を使うプログラムを身近に見せ読みやすくする構文とライブラリと結び付くのである。
モナドとモナド変換子により、関数型か命令型かということは見方の問題になる。


# 練習問題
%%%
tag := "monad-transformer-do-exercises"
%%%

 * {lit}`doug`を、{anchorName doList (module:=DirTree)}`doList`関数の代わりに{kw}`for`を使うように書き直せ。
 * この節で紹介した機能を使ってコードをよくする機会は他にもあるか。あるなら使ってみよ。
