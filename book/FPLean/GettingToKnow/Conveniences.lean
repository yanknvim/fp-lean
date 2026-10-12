module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"


#doc (Manual) "Additional Conveniences" =>
%%%
tag := "getting-to-know-conveniences"
%%%

Leanには、プログラムをずっと簡潔にする便利な機能がいくつかある。

# 暗瞑の引数の自動追加
%%%
tag := "automatic-implicit-parameters"
%%%

:::paragraph
Leanで多相関数を書くとき、通常は暗瞑の引数をすべて列挙する必要はない。
名前を書くだけでよい。
その型をLeanが決められるなら、暗瞑の引数として自動的に挿入される。
つまり、先ほどの{anchorName lengthImp}`length`の定義は、

```anchor lengthImp
def length {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length ys)
```

{anchorTerm lengthImp}`{α : Type}`を書かずに定義できる。

```anchor lengthImpAuto
def length (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length ys)
```

これにより、多くの暗瞑の引数を取る非常に多相的な定義が、大幅に簡単になる。

:::

# パターンマッチングによる定義
%%%
tag := "pattern-matching-definitions"
%%%

{kw}`def`で関数を定義するとき、引数に名前を付けてすぐパターンマッチングに使う、という書き方はよくある。
たとえば{anchorName lengthImpAuto}`length`では、引数{anchorName lengthImpAuto}`xs`は{kw}`match`でしか使っていない。
このような場合は、引数に名前を付けずに、{kw}`match`式の枝を直接書ける。

:::paragraph
まず、引数の型をコロンの右側に移し、戻り値の型を関数型にする。
たとえば{anchorName lengthMatchDef}`length`の型は{anchorTerm lengthMatchDef}`List α → Nat`である。
次に、{lit}`:=`をパターンマッチングの各枝で置き換える。

```anchor lengthMatchDef
def length : List α → Nat
  | [] => 0
  | y :: ys => Nat.succ (length ys)
```

この記法は、二つ以上の引数を取る関数の定義にも使える。
その場合、パターンはコンマで区切る。
たとえば{anchorName drop}`drop`は、数$`n`とリストを受け取り、先頭の$`n`個の要素を取り除いたリストを返す。

```anchor drop
def drop : Nat → List α → List α
  | Nat.zero, xs => xs
  | _, [] => []
  | Nat.succ n, x :: xs => drop n xs
```

:::

:::paragraph

名前付きの引数とパターンは、同じ定義の中で併用できる。
たとえば、既定値と省略可能な値を受け取り、省略可能な値が{anchorName fromOption}`none`なら既定値を返す関数は次のように書ける。

```anchor fromOption
def fromOption (default : α) : Option α → α
  | none => default
  | some x => x
```

この関数は標準ライブラリでは{anchorTerm fragments}`Option.getD`といい、ドット記法で呼び出せる。

```anchor getD
#eval (some "salmonberry").getD ""
```


```anchorInfo getD
"salmonberry"
```


```anchor getDNone
#eval none.getD ""
```


```anchorInfo getDNone
""
```

:::

# ローカル定義
%%%
tag := "local-definitions"
%%%

計算の途中の結果に名前を付けておくと役に立つことが多い。
多くの場合、途中の値はそれ自体が意味のある概念であり、名前を付けておくとプログラムが読みやすくなる。
そうでなくても、途中の値を二度以上使うことがある。
他の多くの言語と同じく、Leanで同じコードを二度書くと二度計算される。結果を変数に入れておけば、計算結果が保存されて再利用される。

:::paragraph

たとえば{anchorName unzipBad}`unzip`は、組のリストをリストの組に変換する関数である。
組のリストが空なら、{anchorName unzipBad}`unzip`の結果は空のリストの組である。
組のリストの先頭に組があるなら、その組の二つのフィールドを、残りのリストをunzipした結果に加える。
この{anchorName unzipBad}`unzip`の定義は、その説明のとおりに書かれている。

```anchor unzipBad
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    (x :: (unzip xys).fst, y :: (unzip xys).snd)
```

残念ながら、ここには問題がある。このコードは必要以上に遅いのである。
組のリストの各要素について再帰呼び出しが二回行われるため、この関数は指数時間かかる。
しかし、二つの再帰呼び出しは同じ結果になるので、二度呼び出す理由はない。
:::

:::paragraph
Leanでは、{kw}`let`を使って再帰呼び出しの結果に名前を付け、保存できる。
{kw}`let`によるローカル定義は、{kw}`def`によるトップレベルの定義と似ている。ローカルに定義する名前、必要なら引数、型シグネチャを取り、{lit}`:=`に続けて本体を書く。
ローカル定義の後ろには、その定義が使える式（{kw}`let`式の*本体*と呼ぶ）を新しい行に書き、ファイル内の桁位置を{kw}`let`キーワードと同じかそれより左にする必要がある。
{anchorName unzip}`unzip`での{kw}`let`によるローカル定義は次のようになる。

```anchor unzip
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped : List α × List β := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)
```

{kw}`let`を1行で使うには、ローカル定義と本体をセミコロンで区切る。
:::

:::paragraph
{kw}`let`によるローカル定義でも、一つのパターンでデータ型の全場合に一致するときはパターンマッチングを使える。
{anchorName unzip}`unzip`の場合、再帰呼び出しの結果は組である。
組のコンストラクタは一つだけなので、名前{anchorName unzip}`unzipped`を組のパターンで置き換えられる。

```anchor unzipPat
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let (xs, ys) : List α × List β := unzip xys
    (x :: xs, y :: ys)
```

{kw}`let`でパターンを適切に使うと、アクセサを手で呼ぶよりコードが読みやすくなる。
:::

:::paragraph
{kw}`let`と{kw}`def`の最大の違いは、再帰的な{kw}`let`定義は{kw}`let rec`と明示しなければならないことである。
たとえば、リストを反転する方法の一つに、再帰的な補助関数を使うものがある。

```anchor reverse
def reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α
    | [], soFar => soFar
    | y :: ys, soFar => helper ys (y :: soFar)
  helper xs []
```

この補助関数は入力のリストをたどり、要素を一つずつ{anchorName reverse}`soFar`に移していく。
入力のリストの終わりに達したとき、{anchorName reverse}`soFar`には入力の逆順が入っている。
:::

# 型推論
%%%
tag := "type-inference"
%%%

:::paragraph
多くの場合、Leanは式の型を自動で決められる。
そのような場合は、トップレベルの定義（{kw}`def`）でもローカル定義（{kw}`let`）でも、型を省略できる。
たとえば、{anchorName unzipNT}`unzip`への再帰呼び出しには注釈が要らない。

```anchor unzipNT
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)
```

:::

目安として、文字列や数値のようなリテラルの型はふつう省略できる。ただし、数値リテラルについてはLeanが意図より狭い型を選ぶことがある。
関数適用の型は、Leanが引数の型と戻り値の型をすでに知っているので、たいてい決められる。
関数定義の戻り値の型の省略は多くの場合うまくいくが、関数の引数には通常注釈が必要である。
関数でない定義、たとえば例の{anchorName unzipNT}`unzipped`は、本体に注釈が要らなければ型注釈も要らない。この定義の本体は関数適用である。

:::paragraph
{kw}`match`式を明示的に使う場合、{anchorName unzipNRT}`unzip`の戻り値の型は省略できる。

```anchor unzipNRT
def unzip (pairs : List (α × β)) :=
  match pairs with
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)
```

:::

:::paragraph

一般に、型注釈は少なすぎるより多すぎる方がよい。
第一に、型を明示すると、コードについての前提が読み手に伝わる。
Leanが型を自分で決められる場合でも、型情報をいちいちLeanに問い合わせずに読める方が楽である。
第二に、型を明示すると、誤りの場所を絞り込みやすい。
型について明示的なプログラムほど、エラーメッセージも情報量が多くなる。
これは、Leanのように表現力の高い型システムを持つ言語ではとくに重要である。
第三に、型を明示すると、そもそもプログラムが書きやすくなる。
型は仕様であり、コンパイラのフィードバックは、その仕様を満たすプログラムを書くための助けになる。
最後に、Leanの型推論はできる範囲で推論する仕組みである。
Leanの型システムは非常に表現力が高いので、すべての式に対して「最良の」あるいは最も一般的な型が存在するわけではない。
つまり、型が得られたとしても、それが用途にとって*正しい*型である保証はない。
たとえば{anchorTerm fourteenNat}`14`は{anchorName length1}`Nat`にも{anchorName fourteenInt}`Int`にもなりうる。

```anchor fourteenNat
#check 14
```


```anchorInfo fourteenNat
14 : Nat
```


```anchor fourteenInt
#check (14 : Int)
```

```anchorInfo fourteenInt
14 : Int
```

:::

:::paragraph
型注釈が足りないと、紛らわしいエラーメッセージが出ることがある。
{anchorName unzipNoTypesAtAll}`unzip`の定義から型をすべて省くと、

```anchor unzipNoTypesAtAll
def unzip pairs :=
  match pairs with
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)
```

{kw}`match`式についてのメッセージが出る。

```anchorError unzipNoTypesAtAll
Invalid match expression: This pattern contains metavariables:
  []
```

{kw}`match`は調べる値の型を知る必要があるのに、その型が分からなかったためである。
「メタ変数」とは、プログラム中の未知の部分のことである。エラーメッセージでは{lit}`?m.XYZ`と書かれる。{ref "polymorphism"}[多相性の節]で説明している。
このプログラムでは、引数の型注釈が必要である。
:::

:::paragraph
ごく簡単なプログラムでも型注釈が要る場合がある。
たとえば恒等関数は、渡された引数をそのまま返すだけである。
引数と戻り値の型注釈を付けると、次のようになる。

```anchor idA
def id (x : α) : α := x
```

Leanは戻り値の型を自分で決められる。

```anchor idB
def id (x : α) := x
```

しかし、引数の型を省くとエラーになる。

```anchor identNoTypes
def id x := x
```


```anchorError identNoTypes
Failed to infer type of binder `x`
```
:::

一般に、「failed to infer」のような文言やメタ変数を含むメッセージは、型注釈を増やす必要があるしるしであることが多い。
とくにLeanを学んでいる間は、ほとんどの型を明示しておくと役に立つ。

# 同時マッチング
%%%
tag := "simultaneous-matching"
%%%

:::paragraph

パターンマッチングの式も、パターンマッチングによる定義と同じく、複数の値に一度にマッチできる。
調べる式も、それにマッチさせるパターンも、コンマで区切って書く。定義に使う記法と同様である。
同時マッチングを使った{anchorName dropMatch}`drop`の版は次のとおりである。

```anchor dropMatch
def drop (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | Nat.zero, ys => ys
  | _, [] => []
  | Nat.succ n , y :: ys => drop n ys
```

:::

:::paragraph

同時マッチングは組に対するマッチングに似ているが、重要な違いがある。
Leanは、マッチさせる式とパターンのつながりを追跡しており、その情報は停止性の検査や静的な型情報の伝播などに使われる。
その結果、組に対してマッチする{anchorName sameLengthPair}`sameLength`は停止性検査に弾かれる。{anchorName sameLengthPair}`xs`と{anchorTerm sameLengthPair}`x :: xs'`のつながりが、間に入った組によって見えなくなるためである。

```anchor sameLengthPair
def sameLength (xs : List α) (ys : List β) : Bool :=
  match (xs, ys) with
  | ([], []) => true
  | (x :: xs', y :: ys') => sameLength xs' ys'
  | _ => false
```

```anchorError sameLengthPair
fail to show termination for
  sameLength
with errors
failed to infer structural recursion:
Not considering parameter α of sameLength:
  it is unchanged in the recursive calls
Not considering parameter β of sameLength:
  it is unchanged in the recursive calls
Cannot use parameter xs:
  failed to eliminate recursive application
    sameLength xs' ys'
Cannot use parameter ys:
  failed to eliminate recursive application
    sameLength xs' ys'


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
              xs ys
1) 1748:28-46  ?  ?
Please use `termination_by` to specify a decreasing measure.
```

両方のリストを同時にマッチさせれば受け入れられる。

```anchor sameLengthOk2
def sameLength (xs : List α) (ys : List β) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => sameLength xs' ys'
  | _, _ => false
```

:::

# 自然数のパターン
%%%
tag := "natural-number-patterns"
%%%

:::paragraph

{ref "datatypes-and-patterns"}[データ型とパターン]の節では、{anchorName even}`even`を次のように定義した。

```anchor even
def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)
```

{anchorName length1}`List.cons`や{anchorName length1}`List.nil`を直接使うよりリストのパターンが読みやすくなる特別な記法があるのと同じように、自然数は数値リテラルと{anchorTerm evenFancy}`+`を使ってマッチできる。
たとえば{anchorName evenFancy}`even`は次のようにも定義できる。

```anchor evenFancy
def even : Nat → Bool
  | 0 => true
  | n + 1 => not (even n)
```

この記法では、{anchorTerm evenFancy}`+`パターンの引数はそれぞれ別の役割を担う。
舞台裏では、左の引数（上の{anchorName evenFancy}`n`）が何個かの{anchorName even}`Nat.succ`パターンの引数になり、右の引数（上の{anchorTerm evenFancy}`1`）がそのパターンを{anchorName even}`Nat.succ`で何重に包むかを決める。
{anchorName explicitHalve}`Nat`を2で割って余りを切り捨てる{anchorName explicitHalve}`halve`の明示的なパターンは、

```anchor explicitHalve
def halve : Nat → Nat
  | Nat.zero => 0
  | Nat.succ Nat.zero => 0
  | Nat.succ (Nat.succ n) => halve n + 1
```

数値リテラルと{anchorTerm halve}`+`で置き換えられる。

```anchor halve
def halve : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => halve n + 1
```

舞台裏では、この二つの定義は完全に同等である。
念のため、{anchorTerm halve}`halve n + 1`は{anchorTerm halveParens}`(halve n) + 1`と同じであり、{anchorTerm halveParens}`halve (n + 1)`ではない。

:::

:::paragraph

この記法を使うとき、{anchorTerm halveFlippedPat}`+`の二番目の引数は必ず{anchorName halveFlippedPat}`Nat`のリテラルにする。
加法は可換だが、パターンの中で引数を入れ替えると次のようなエラーになる。

```anchor halveFlippedPat
def halve : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 + n => halve n + 1
```

```anchorError halveFlippedPat
Invalid pattern(s): `n` is an explicit pattern variable, but it only occurs in positions that are inaccessible to pattern matching:
  .(Nat.add 2 n)
```

この制限により、パターン中の{anchorTerm halveFlippedPat}`+`記法をすべて基になる{anchorName even}`Nat.succ`の使用に変換でき、舞台裏の言語が簡単になる。

:::

# 無名関数
%%%
tag := "anonymous-functions"
%%%

:::paragraph

Leanの関数は、トップレベルで定義しなくてもよい。
式として関数を作るには{kw}`fun`の記法を使う。
関数式は{kw}`fun`というキーワードで始まり、その後に一つ以上の引数を書き、戻り値の式とは{lit}`=>`で区切る。
たとえば、数に1を足す関数は次のように書ける。

```anchor incr
#check fun x => x + 1
```

```anchorInfo incr
fun x => x + 1 : Nat → Nat
```

型注釈は{kw}`def`と同じく、括弧とコロンで書く。

```anchor incrInt
#check fun (x : Int) => x + 1
```


```anchorInfo incrInt
fun x => x + 1 : Int → Int
```

同様に、暗瞑の引数は淡括弧で書ける。

```anchor identLambda
#check fun {α : Type} (x : α) => x
```

```anchorInfo identLambda
fun {α} x => x : {α : Type} → α → α
```

この形の無名関数式は*ラムダ式*と呼ばれることが多い。プログラミング言語を数学的に記述するときの記法では、Leanの{kw}`fun`キーワードにあたる場所にギリシャ文字のλ（ラムダ）を使うためである。
Leanでは{kw}`fun`の代わりに{kw}`λ`も使えるが、{kw}`fun`と書くのが最も一般的である。

:::

:::paragraph

無名関数でも、{kw}`def`で使う複数パターンの書き方が使える。
たとえば、自然数の前者があればそれを返す関数は次のように書ける。

```anchor predHuh
#check fun
  | 0 => none
  | n + 1 => some n
```


```anchorInfo predHuh
fun x =>
  match x with
  | 0 => none
  | n.succ => some n : Nat → Option Nat
```

Lean自身によるこの関数の表示では、名前付きの引数と{kw}`match`式になっている。
Leanの便利な構文糖の多くは、舞台裏ではより単純な構文に展開される。その抽象化がときには漏れ見えるのである。

:::

:::paragraph

引数を取る{kw}`def`の定義は、関数式として書き直せる。
たとえば、引数を2倍する関数は次のように書ける。

```anchor doubleLambda
def double : Nat → Nat := fun
  | 0 => 0
  | k + 1 => double k + 2
```


{anchorEvalStep incrSteps 0}`fun x => x + 1`のようにごく簡単な無名関数では、関数を作るための記法がやや冗長になる。
この例では、関数を導入するのに空白を除いて6文字を使っているのに対し、本体は空白を除いて3文字しかない。
このような簡単な場合のために、Leanには省略記法がある。
括弧で囲んだ式の中で、中央の点{anchorTerm incrSteps}`·`を引数の代わりに使うことができ、括弧の中の式が関数の本体になる。
この関数は{anchorEvalStep incrSteps 1}`(· + 1)`とも書ける。
:::

:::paragraph

中央の点は、常に、それを囲む*最も内側の*括弧の組から関数を作る。
たとえば{anchorEvalStep funPair 0}`(· + 5, 3)`は数の組を返す関数であり、{anchorEvalStep pairFun 0}`((· + 5), 3)`は関数と数の組である。
点を複数使うと、左から順に引数になる。

```anchorEvalSteps twoDots
(· , ·) 1 2
===>
(1, ·) 2
===>
(1, 2)
```

無名関数は、{kw}`def`や{kw}`let`で定義した関数とまったく同じように適用できる。
{anchor applyLambda}`#eval (fun x => x + x) 5`というコマンドの結果は次のようになる。

```anchorInfo applyLambda
10
```

{anchor applyCdot}`#eval (· * 2) 5`の結果は次のようになる。

```anchorInfo applyCdot
10
```

:::

# 名前空間
%%%
tag := "namespaces"
%%%

Leanの名前はそれぞれ*名前空間*の中にあり、名前空間は名前の集まりである。
名前は{lit}`.`を使って名前空間に置かれる。たとえば{anchorName fragments}`List.map`は{lit}`List`名前空間の{anchorName fragments}`map`という名前である。
別の名前空間にある名前は、それ以外が同じでも衝突しない。
つまり、{anchorName fragments}`List.map`と{anchorName fragments}`Array.map`は別の名前である。
名前空間は入れ子にできる。たとえば{lit}`Project.Frontend.User.loginTime`は、入れ子になった名前空間{lit}`Project.Frontend.User`にある{lit}`loginTime`という名前である。

:::paragraph
名前は名前空間の中で直接定義できる。
たとえば{anchorName fragments}`double`という名前を{anchorName even}`Nat`名前空間に定義できる。

```anchor NatDouble
def Nat.double (x : Nat) : Nat := x + x
```

{anchorName even}`Nat`は型の名前でもあるので、{anchorName even}`Nat`型の式に対して{anchorName fragments}`Nat.double`を呼ぶのにドット記法が使える。

```anchor NatDoubleFour
#eval (4 : Nat).double
```

```anchorInfo NatDoubleFour
8
```

:::

:::paragraph

名前を名前空間の中で直接定義するほかに、{kw}`namespace`と{kw}`end`のコマンドを使って一連の宣言を名前空間に置ける。
たとえば、これは{lit}`NewNamespace`名前空間に{anchorName NewNamespace}`triple`と{anchorName NewNamespace}`quadruple`を定義する。

```anchor NewNamespace
namespace NewNamespace
def triple (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat := 2 * x + 2 * x
end NewNamespace
```

参照するには、名前の前に{lit}`NewNamespace.`を付ける。

```anchor tripleNamespace
#check NewNamespace.triple
```

```anchorInfo tripleNamespace
NewNamespace.triple (x : Nat) : Nat
```


```anchor quadrupleNamespace
#check NewNamespace.quadruple
```

```anchorInfo quadrupleNamespace
NewNamespace.quadruple (x : Nat) : Nat
```

:::

:::paragraph
名前空間は*開く*ことができ、中の名前を修飾なしで使えるようになる。
式の前に{kw}`open` {lit}`MyNamespace `{kw}`in`と書くと、その式の中で{lit}`MyNamespace`の中身が使えるようになる。
たとえば{anchorName quadrupleOpenDef}`timesTwelve`は、{anchorTerm NewNamespace}`NewNamespace`を開いたうえで{anchorName quadrupleOpenDef}`quadruple`と{anchorName quadrupleOpenDef}`triple`の両方を使っている。

```anchor quadrupleOpenDef
def timesTwelve (x : Nat) :=
  open NewNamespace in
  quadruple (triple x)
```

:::

:::paragraph
名前空間はコマンドの前で開くこともできる。
これにより、一つの式だけでなく、そのコマンドのすべての部分から名前空間の中身を参照できる。
このためには、コマンドの前に{kw}`open`{lit}` ... `{kw}`in`を置く。

```anchor quadrupleNamespaceOpen
open NewNamespace in
#check quadruple
```

```anchorInfo quadrupleNamespaceOpen
NewNamespace.quadruple (x : Nat) : Nat
```

関数のシグネチャには、名前の完全な名前空間が表示される。
さらに、ファイルの残りにある*以降すべての*コマンドに対して名前空間を開くこともできる。
そのためには、トップレベルで使う{kw}`open`から{kw}`in`を省くだけでよい。

:::

# {lit}`if let`
%%%
tag := "if-let"
%%%

:::paragraph
直和型の値を扱うとき、関心があるコンストラクタが一つだけということがよくある。
たとえば、Markdownのインライン要素の一部を表す次の型を考える。

```anchor Inline
inductive Inline : Type where
  | lineBreak
  | string : String → Inline
  | emph : Inline → Inline
  | strong : Inline → Inline
```

文字列の要素を見分けて中身を取り出す関数は次のように書ける。

```anchor inlineStringHuhMatch
def Inline.string? (inline : Inline) : Option String :=
  match inline with
  | Inline.string s => some s
  | _ => none
```

:::

:::paragraph
この関数の本体は、{kw}`if`と{kw}`let`を組み合わせても書ける。

```anchor inlineStringHuh
def Inline.string? (inline : Inline) : Option String :=
  if let Inline.string s := inline then
    some s
  else none
```

これは、パターンマッチングの{kw}`let`記法とよく似ている。
違いは、{kw}`else`の場合に代替の処理を書けるので、直和型にも使えることである。
{kw}`match`の代わりに{kw}`if let`を使うと、コードが読みやすくなる場面もある。

:::

# 構造体の引数の位置指定
%%%
tag := "positional-structure-arguments"
%%%

{ref "structures"}[構造体の節]では、構造体を作る二つの方法を紹介した。
 1. {anchorTerm pointCtor}`Point.mk 1 2`のように、コンストラクタを直接呼ぶ。
 2. {anchorTerm pointBraces}`{ x := 1, y := 2 }`のように、淡括弧の記法を使う。

場面によっては、コンストラクタの名前を直接書かずに、名前ではなく位置で引数を渡せると便利である。
たとえば、似た構造体をいくつも定義すると分野の概念を分けておけるが、コードを自然に読むときには、どれも本質的には組として扱いたいこともある。
そのような場合は、引数を山括弧{lit}`⟨`と{lit}`⟩`で囲める。
{anchorName pointBraces}`Point`は{anchorTerm pointPos}`⟨1, 2⟩`と書ける。
注意が必要である。
不等号の{lit}`<`と{lit}`>`に似ているが、これらは別の括弧である。
それぞれ{lit}`\<`と{lit}`\>`で入力できる。

:::paragraph
名前付きのコンストラクタ引数に淡括弧の記法を使う場合と同じく、この位置指定の記法は、型注釈やプログラム中の他の型情報から構造体の型をLeanが決められる場面でしか使えない。
たとえば{anchorTerm pointPosEvalNoType}`#eval ⟨1, 2⟩`は次のエラーになる。

```anchorError pointPosEvalNoType
Invalid `⟨...⟩` notation: The expected type of this term could not be determined
```

このエラーは、使える型情報がないために起こる。
{anchorTerm pointPosWithType}`#eval (⟨1, 2⟩ : Point)`のように注釈を付ければ解決する。

```anchorInfo pointPosWithType
{ x := 1.000000, y := 2.000000 }
```

:::

# 文字列補間
%%%
tag := "string-interpolation"
%%%

:::paragraph
Leanでは、文字列の前に{kw}`s!`を付けると*補間*が働き、文字列中の淡括弧で囲んだ式がその値で置き換えられる。
これはPythonの{python}`f`文字列やC#の{CSharp}`$`付き文字列に似ている。
たとえば、

```anchor interpolation
#eval s!"three fives is {NewNamespace.triple 5}"
```

と出力される。

```anchorInfo interpolation
"three fives is 15"
```

:::

:::paragraph
すべての式を文字列に補間できるわけではない。
たとえば、関数を補間しようとするとエラーになる。

```anchor interpolationOops
#check s!"three fives is {NewNamespace.triple}"
```

とエラーになる。

```anchorError interpolationOops
failed to synthesize instance of type class
  ToString (Nat → Nat)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

関数を文字列に変換する標準的な方法がないためである。
コンパイラは、いろいろな型の式を評価した結果をどう表示するかを記した表を持っているのと同じように、いろいろな型の値を文字列に変換する方法を記した表も持っている。
{lit}`failed to synthesize instance`というメッセージは、Leanコンパイラがその型に対する項目をこの表に見つけられなかったという意味である。
この仕組みの詳細と、表に新しい項目を追加する方法は{ref "type-classes"}[型クラス]の章で説明する。
:::
