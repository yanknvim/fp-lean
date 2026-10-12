module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.DependentTypes"

#doc (Manual) "Indexed Families" =>
%%%
tag := "indexed-families"
%%%

多相的な帰納型は型引数を取る。
たとえば{moduleName}`List`はリストの要素の型を決める引数を取り、{moduleName}`Except`は例外か値の型を決める引数を取る。
データ型のどのコンストラクタでも同じであるこれらの型引数を*パラメータ*と呼ぶ。

しかし、帰納型の引数がどのコンストラクタでも同じである必要はない。
型への引数がコンストラクタの選択によって変わる帰納型を*添字付き族*と呼び、変わる引数を*添字*と呼ぶ。
添字付き族の「hello world」は、要素の型に加えてリストの長さを持つリストの型で、慣例的に「ベクトル」と呼ばれる。

```anchor Vect
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
```

{anchorName vect3}`String`が三つ入ったベクトルの型には、{anchorName vect3}`String`が三つ入っているという事実が含まれる。

```anchor vect3
example : Vect String 3 :=
  .cons "one" (.cons "two" (.cons "three" .nil))
```


関数の宣言では、コロンの前にいくつかの引数を置いて定義全体で使えることを示し、コロンの後にいくつかの引数を置いて、それらでパターンマッチングして場合ごとに関数を定義したいことを示せる。
帰納的データ型にも同様の原則がある。引数{anchorName Vect}`α`はデータ型の宣言の先頭、コロンの前に名前を書く。これは、定義の中で{anchorName Vect}`Vect`が現れるすべての箇所で最初の引数として与えねばならないパラメータであることを示す。一方、{anchorName Vect}`Nat`の引数はコロンの後にあり、変わりうる添字であることを示す。
実際、{anchorName Vect}`nil`と{anchorName Vect}`cons`のコンストラクタ宣言で{anchorName Vect}`Vect`が現れる三箇所は、いずれも{anchorName Vect}`α`を最初の引数として与え、二つ目の引数はそれぞれ異なっている。



{anchorName Vect}`nil`の宣言は、それが型{anchorTerm Vect}`Vect α 0`のコンストラクタであることを述べている。
つまり、{anchorTerm nilNotLengthThree}`Vect String 3`を期待する文脈で{anchorName nilNotLengthThree}`Vect.nil`を使うと型エラーになる。{anchorTerm otherEx}`List String`を期待する文脈で{anchorTerm otherEx}`[1, 2, 3]`が型エラーになるのと同じである。
```anchor nilNotLengthThree
example : Vect String 3 := Vect.nil
```
```anchorError nilNotLengthThree
Type mismatch
  Vect.nil
has type
  Vect ?m.3 0
but is expected to have type
  Vect String 3
```
この例で{anchorTerm Vect}`0`と{anchorTerm nilNotLengthThree}`3`が食い違うのは、{anchorTerm Vect}`0`と{anchorTerm nilNotLengthThree}`3`自体が型でないにもかかわらず、他の型の食い違いとまったく同じ役割を果たす。
メッセージにあるメタ変数は無視してよい。それが現れるのは、{anchorName otherEx}`Vect.nil`がどの要素の型でも持ちうることを示すためである。

添字付き族が型の*族*と呼ばれるのは、添字の値が違えば使えるコンストラクタが変わりうるためである。
ある意味で、添字付き族は一つの型ではなく、関連する型の集まりであり、添字の値を選ぶことがその集まりから型を選ぶことにもなる。
{anchorName Vect}`Vect`の添字として{anchorTerm otherEx}`5`を選べばコンストラクタ{anchorName Vect}`cons`だけが使え、添字として{anchorTerm Vect}`0`を選べば{anchorName Vect}`nil`だけが使える。

添字がまだ分かっていない場合（たとえば変数であるため）は、分かるまでどのコンストラクタも使えない。
長さに{anchorName nilNotLengthN}`n`を使うと、{anchorName otherEx}`Vect.nil`も{anchorName consNotLengthN}`Vect.cons`も使えない。変数{anchorName nilNotLengthN}`n`が{anchorTerm Vect}`0`に一致する{anchorName Vect}`Nat`を表すのか{anchorTerm Vect}`n + 1`を表すのかを知る手立てがないためである。
```anchor nilNotLengthN
example : Vect String n := Vect.nil
```
```anchorError nilNotLengthN
Type mismatch
  Vect.nil
has type
  Vect ?m.2 0
but is expected to have type
  Vect String n
```
```anchor consNotLengthN
example : Vect String n := Vect.cons "Hello" (Vect.cons "world" Vect.nil)
```
```anchorError consNotLengthN
Type mismatch
  Vect.cons "Hello" (Vect.cons "world" Vect.nil)
has type
  Vect String (0 + 1 + 1)
but is expected to have type
  Vect String n
```

リストの長さを型の一部に持つということは、その型がより多くの情報を持つということである。
たとえば{anchorName replicateStart}`Vect.replicate`は、与えられた値の複製をいくつか入れた{anchorName replicateStart}`Vect`を作る関数である。
これを正確に述べる型は次のとおりである。
```anchor replicateStart
def Vect.replicate (n : Nat) (x : α) : Vect α n := _
```
引数{anchorName replicateStart}`n`が結果の長さとして現れる。
アンダースコアの穴埋めに対応するメッセージが、目の前の作業を説明する。
```anchorError replicateStart
don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
⊢ Vect α n
```

添字付き族を扱うときは、コンストラクタの添字が期待される型の添字に一致するとLeanに見えるときにだけ、そのコンストラクタを適用できる。
しかし、どちらのコンストラクタの添字も{anchorName replicateStart}`n`には一致しない。{anchorName Vect}`nil`は{anchorName otherEx}`Nat.zero`に、{anchorName Vect}`cons`は{anchorName otherEx}`Nat.succ`に一致する。
先ほどの型エラーの例と同じく、変数{anchorName Vect}`n`は、関数に引数としてどの{anchorName Vect}`Nat`が与えられるかによって、どちらをも表しうる。
解決策は、パターンマッチングで二つの可能な場合の両方を考えることである。
```anchor replicateMatchOne
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => _
  | k + 1 => _
```
{anchorName replicateStart}`n`が期待される型に現れるので、{anchorName replicateStart}`n`でパターンマッチングすると、マッチの二つの場合で期待される型が*洗練*される。
一つ目のアンダースコアでは、期待される型が{lit}`Vect α 0`になっている。
```anchorError replicateMatchOne
don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
⊢ Vect α 0
```
二つ目のアンダースコアでは、{lit}`Vect α (k + 1)`になっている。
```anchorError replicateMatchTwo
don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
k : Nat
⊢ Vect α (k + 1)
```
パターンマッチングが値の構造を明らかにするだけでなくプログラムの型を洗練するとき、それを*依存パターンマッチング*と呼ぶ。

洗練された型により、コンストラクタを適用できる。
一つ目のアンダースコアは{anchorName otherEx}`Vect.nil`に、二つ目は{anchorName consNotLengthN}`Vect.cons`に一致する。
```anchor replicateMatchFour
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons _ _
```
{anchorName replicateMatchFour}`.cons`の下の一つ目のアンダースコアの型は{anchorName replicateMatchFour}`α`であるべきである。
使える{anchorName replicateMatchFour}`α`があり、それは{anchorName replicateMatchFour}`x`である。
```anchorError replicateMatchFour
don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
k : Nat
⊢ α
```
二つ目のアンダースコアの型は{lit}`Vect α k`であるべきで、{anchorName replicate}`replicate`への再帰呼び出しで作れる。
```anchorError replicateMatchFive
don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
k : Nat
⊢ Vect α k
```
これが{anchorName replicate}`replicate`の最終的な定義である。

```anchor replicate
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x (replicate k x)
```

{anchorName replicate}`Vect.replicate`の情報量の多い型は、関数を書くときの助けになるだけでなく、利用側のコードがソースコードを読まずに、予想外の関数をいくつも排除できるようにする。
リスト用の{anchorName listReplicate}`replicate`の版は、間違った長さのリストを作りうる。

```anchor listReplicate
def List.replicate (n : Nat) (x : α) : List α :=
  match n with
  | 0 => []
  | k + 1 => x :: x :: replicate k x
```
しかし、{anchorName replicateOops}`Vect.replicate`でこの間違いをすると型エラーになる。
```anchor replicateOops
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x (.cons x (replicate k x))
```
```anchorError replicateOops
Application type mismatch: The argument
  cons x (replicate k x)
has type
  Vect α (k + 1)
but is expected to have type
  Vect α k
in the application
  cons x (cons x (replicate k x))
```


{anchorName otherEx}`List.zip`関数は、一つ目のリストの最初の要素と二つ目のリストの最初の要素、一つ目のリストの二番目の要素と二つ目のリストの二番目の要素、という具合に組にして二つのリストをまとめる。
{anchorName otherEx}`List.zip`を使うと、アメリカのオレゴン州で最も高い三つの山と、デンマークで最も高い三つの地点を組にできる。
```anchorTerm zip1
["Mount Hood",
 "Mount Jefferson",
 "South Sister"].zip ["Møllehøj", "Yding Skovhøj", "Ejer Bavnehøj"]
```
結果は三つの組のリストになる。
```anchorTerm zip1
[("Mount Hood", "Møllehøj"),
 ("Mount Jefferson", "Yding Skovhøj"),
 ("South Sister", "Ejer Bavnehøj")]
```
リストの長さが違うときにどうなるべきかは、いくらかはっきりしない。
多くの言語と同じく、Leanは一方のリストの余分な要素を無視することを選んでいる。
たとえば、オレゴンで最も高い五つの山の標高と、デンマークで最も高い三つの地点の標高を組み合わせると、三つの組になる。
特に、
```anchorTerm zip2
[3428.8, 3201, 3158.5, 3075, 3064].zip [170.86, 170.77, 170.35]
```
は次のように評価される。
```anchorTerm zip2
[(3428.8, 170.86), (3201, 170.77), (3158.5, 170.35)]
```

このやり方は常に答えを返すので便利だが、リストの長さが意図せず違うときにデータを捨ててしまう危険がある。
F#は別のやり方を取る。F#の{fsharp}`List.zip`は長さが一致しないときに例外を投げる。次の{lit}`fsi`の対話に見られる。
```fsharp
> List.zip [3428.8; 3201.0; 3158.5; 3075.0; 3064.0] [170.86; 170.77; 170.35];;
```
```fsharpError
System.ArgumentException: The lists had different lengths.
list2 is 2 elements shorter than list1 (Parameter 'list2')
   at Microsoft.FSharp.Core.DetailedExceptions.invalidArgDifferentListLength[?](String arg1, String arg2, Int32 diff) in /builddir/build/BUILD/dotnet-v3.1.424-SDK/src/fsharp.3ef6f0b514198c0bfa6c2c09fefe41a740b024d5/src/fsharp/FSharp.Core/local.fs:line 24
   at Microsoft.FSharp.Primitives.Basics.List.zipToFreshConsTail[a,b](FSharpList`1 cons, FSharpList`1 xs1, FSharpList`1 xs2) in /builddir/build/BUILD/dotnet-v3.1.424-SDK/src/fsharp.3ef6f0b514198c0bfa6c2c09fefe41a740b024d5/src/fsharp/FSharp.Core/local.fs:line 918
   at Microsoft.FSharp.Primitives.Basics.List.zip[T1,T2](FSharpList`1 xs1, FSharpList`1 xs2) in /builddir/build/BUILD/dotnet-v3.1.424-SDK/src/fsharp.3ef6f0b514198c0bfa6c2c09fefe41a740b024d5/src/fsharp/FSharp.Core/local.fs:line 929
   at Microsoft.FSharp.Collections.ListModule.Zip[T1,T2](FSharpList`1 list1, FSharpList`1 list2) in /builddir/build/BUILD/dotnet-v3.1.424-SDK/src/fsharp.3ef6f0b514198c0bfa6c2c09fefe41a740b024d5/src/fsharp/FSharp.Core/list.fs:line 466
   at <StartupCode$FSI_0006>.$FSI_0006.main@()
Stopped due to error
```
これで情報をうっかり捨てることは避けられるが、プログラムを落とすことにはそれ自体の難しさがある。
Leanで相当するものは{anchorName otherEx}`Option`や{anchorName otherEx}`Except`モナドを使うことになるが、その安全性に見合わない負担を持ち込むことになる。

:::paragraph
しかし{anchorName Vect}`Vect`を使えば、両方の引数が同じ長さであることを要求する型を持つ{anchorName VectZip}`zip`の版を書ける。

```anchor VectZip
def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)
```

この定義には、両方の引数が{anchorName otherEx}`Vect.nil`である場合か、両方が{anchorName consNotLengthN}`Vect.cons`である場合のパターンしかない。そしてLeanは、{anchorName otherEx}`List`に対する同様の定義で生じるような「場合の欠落」のエラーなしにこの定義を受け付ける。
```anchor zipMissing
def List.zip : List α → List β → List (α × β)
  | [], [] => []
  | x :: xs, y :: ys => (x, y) :: zip xs ys
```
```anchorError zipMissing
Missing cases:
[], (List.cons _ _)
(List.cons _ _), []
```
:::

これは、一つ目のパターンで使うコンストラクタ{anchorName Vect}`nil`か{anchorName Vect}`cons`が、長さ{anchorName VectZip}`n`についての型検査器の知識を*洗練*するためである。
一つ目のパターンが{anchorName Vect}`nil`なら、型検査器は長さが{anchorTerm VectZipLen}`0`だったとさらに判断できるので、二つ目のパターンとして可能な選択は{anchorName Vect}`nil`だけである。
同様に、一つ目のパターンが{anchorName Vect}`cons`なら、型検査器はある{anchorName VectZipLen}`Nat` {anchorName VectZipLen}`k`について長さが{anchorTerm VectZipLen}`k+1`だったと判断できるので、二つ目のパターンとして可能な選択は{anchorName Vect}`cons`だけである。
実際、{anchorName Vect}`nil`と{anchorName Vect}`cons`を一緒に使う場合を加えると、長さが一致しないので型エラーになる。
```anchor zipExtraCons
def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .nil, .cons y ys => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)
```
```anchorError zipExtraCons
Type mismatch
  Vect.cons y ys
has type
  Vect ?m.10 (?m.16 + 1)
but is expected to have type
  Vect β 0
```
長さの洗練は、{anchorName VectZipLen}`n`を明示的な引数にすると見られる。

```anchor VectZipLen
def Vect.zip : (n : Nat) → Vect α n → Vect β n → Vect (α × β) n
  | 0, .nil, .nil => .nil
  | k + 1, .cons x xs, .cons y ys => .cons (x, y) (zip k xs ys)
```

# 練習問題
%%%
tag := "indexed-families-exercises"
%%%


依存型を使ったプログラミングの感覚をつかむには経験が要り、この節の練習問題はとても重要である。
各練習問題では、コードを試しながら、型検査器が捕まえられる間違いと捕まえられない間違いがどれかを考えてみるとよい。
これはエラーメッセージの感覚を養うのにもよい。

 * オレゴンで最も高い三つの山とデンマークで最も高い三つの地点を組み合わせるときに、{anchorName VectZip}`Vect.zip`が正しい答えを出すことを確かめよ。
   {anchorName Vect}`Vect`には{anchorName otherEx}`List`のような糖衣構文がないので、まず{anchorTerm exerciseDefs}`oregonianPeaks : Vect String 3`と{anchorTerm exerciseDefs}`danishPeaks : Vect String 3`を定義するとよい。

 * 型{anchorTerm exerciseDefs}`(α → β) → Vect α n → Vect β n`の{anchorName exerciseDefs}`Vect.map`関数を定義せよ。

 * {anchorName Vect}`Vect`の要素を関数と一つずつ組み合わせる{anchorName exerciseDefs}`Vect.zipWith`関数を定義せよ。
   型は{anchorTerm exerciseDefs}`(α → β → γ) → Vect α n → Vect β n → Vect γ n`とする。

 * 組の{anchorName Vect}`Vect`を{anchorName Vect}`Vect`の組に分ける{anchorName exerciseDefs}`Vect.unzip`関数を定義せよ。型は{anchorTerm exerciseDefs}`Vect (α × β) n → Vect α n × Vect β n`とする。

 * {anchorName Vect}`Vect`の*末尾*に要素を加える{anchorName exerciseDefs}`Vect.push`関数を定義せよ。 型は{anchorTerm exerciseDefs}`Vect α n → α → Vect α (n + 1)`とし、{anchorTerm snocSnowy}`#eval Vect.push (.cons "snowy" .nil) "peaks"`が{anchorInfo snocSnowy}`Vect.cons "snowy" (Vect.cons "peaks" (Vect.nil))`になることを確かめよ。

 * {anchorName Vect}`Vect`の順序を逆にする{anchorName exerciseDefs}`Vect.reverse`関数を定義せよ。

 * 次の型の{anchorName exerciseDefs}`Vect.drop`関数を定義せよ: {anchorTerm exerciseDefs}`(n : Nat) → Vect α (k + n) → Vect α k`。
   {anchorTerm ejerBavnehoej}`#eval danishPeaks.drop 2`が{anchorInfo ejerBavnehoej}`Vect.cons "Ejer Bavnehøj" (Vect.nil)`になることを確かめて、働くことを検証せよ。

 * {anchorName Vect}`Vect`の最初の{anchorName take}`n`個の要素を返す、型{anchorTerm take}`(n : Nat) → Vect α (k + n) → Vect α n`の{anchorName take}`Vect.take`関数を定義せよ。例で働くことを確かめよ。
