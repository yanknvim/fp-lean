module
public import VersoManual
import FPLean.Examples



open Verso.Genre Manual
open Verso Code External

open FPLean

example_module Examples.Intro

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"

#doc (Manual) "Datatypes and Patterns" =>
%%%
tag := "datatypes-and-patterns"
%%%

構造体を使うと、独立した複数のデータを一つのまとまった全体にまとめ、それを新しい型として表せる。
構造体のように値の集まりをまとめる型を*直積型*と呼ぶ。
しかし、多くの概念は構造体としては自然に表せない。
たとえば、アプリケーションで利用者の権限を扱うとする。ある利用者は文書の所有者で、ある利用者は文書を編集でき、別の利用者は読むだけかもしれない。
電卓には、加算、減算、乗算のようないくつかの二項演算子がある。
構造体には、複数の選択肢を表す簡単な方法がない。

同様に、構造体は決まった個数のフィールドをまとめるのには向いているが、アプリケーションによっては、要素の個数が決まっていないデータを扱う必要がある。
木やリストのような古典的なデータ構造の多くは再帰的な構造を持つ。リストの残りがまたリストであり、二分木の左右の枝がまた二分木である、といった具合である。
先ほどの電卓では、式そのものの構造が再帰的である。
たとえば、加算の式の被加数が、それ自体乗算の式であることがある。

選択肢を持つデータ型を*直和型*、自分自身を含められるデータ型を*再帰的データ型*と呼ぶ。
再帰的な直和型を*帰納的データ型*と呼ぶ。数学的帰納法でその性質を証明できるためである。
プログラミングでは、帰納的データ型はパターンマッチングと再帰関数によって扱う。

:::paragraph
組み込みの型の多くは、実は標準ライブラリで定義された帰納的データ型である。
たとえば{anchorName Bool}`Bool`は帰納的データ型である。

```anchor Bool
inductive Bool where
  | false : Bool
  | true : Bool
```

この定義には二つの主要な部分がある。
最初の行が新しい型の名前（{anchorName Bool}`Bool`）を与え、残りの行がそれぞれコンストラクタを記述する。
構造体のコンストラクタと同じく、帰納的データ型のコンストラクタは、任意の初期化や検証のコードを書く場所ではなく、他のデータを受け取って入れておくだけのものである。
構造体と違い、帰納的データ型は複数のコンストラクタを持てる。
ここでは{anchorName Bool}`true`と{anchorName Bool}`false`の二つのコンストラクタがあり、どちらも引数を取らない。
構造体の宣言がその名前を型名の名前空間に置くのと同じように、帰納的データ型はコンストラクタの名前を名前空間に置く。
Leanの標準ライブラリでは、{anchorName BoolNames}`true`と{anchorName BoolNames}`false`がこの名前空間から再輸出されているので、それぞれ{anchorName BoolNames}`Bool.true`、{anchorName BoolNames}`Bool.false`と書かずに、そのまま書ける。
:::

:::paragraph
データモデリングの観点では、帰納的データ型は、他の言語でシールされた抽象クラスを使うような場面の多くで使う。
C#やJavaのような言語では、{anchorName Bool}`Bool`を次のように定義するかもしれない。
```CSharp
abstract class Bool {}
class True : Bool {}
class False : Bool {}
```
ただし、両者の表現はかなり異なる。とくに、抽象でないクラスはそれぞれ新しい型を作り、同時にデータを割り当てる新しい方法も作る。オブジェクト指向の例では、{CSharp}`True`と{CSharp}`False`はいずれも{CSharp}`Bool`より具体的な型であるが、Leanの定義が導入する型は{anchorName Bool}`Bool`だけである。
:::

負でない整数の型{anchorName Nat}`Nat`も帰納的データ型である。

```anchor Nat
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
```

ここで{anchorName NatNames}`zero`が0を、{anchorName NatNames}`succ`が他の数の後者を表す。
{anchorName NatNames}`succ`の宣言に出てくる{anchorName Nat}`Nat`は、まさにこれから定義しようとしている型{anchorName Nat}`Nat`である。
*後者*とは「1だけ大きい数」のことである。5の後者は6、32,185の後者は32,186である。
この定義では、{anchorEvalStep four 1}`4`は{anchorEvalStep four 0}`Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))`と表される。
この定義は、名前が少し違うだけで{anchorName even}`Bool`の定義とほぼ同じである。
実際の違いは、{anchorName NatNames}`succ`の後ろに{anchorTerm Nat}`(n : Nat)`が付いていることだけである。これは、コンストラクタ{anchorName NatNames}`succ`が{anchorName Nat}`Nat`型の引数を取り、その名前が{anchorName Nat}`n`であることを示している。
{anchorName NatNames}`zero`と{anchorName NatNames}`succ`は型名の名前空間に入っているので、それぞれ{anchorName NatNames}`Nat.zero`、{anchorName NatNames}`Nat.succ`として参照する必要がある。

{anchorName Nat}`n`のような引数の名前は、Leanのエラーメッセージや、証明を書くときのフィードバックに現れることがある。
Leanには、引数を名前で指定するための省略可能な記法もある。
ただし一般には、引数の名前は構造体のフィールド名ほど重要ではない。APIの一部として占める割合が小さいためである。

C#やJavaでは、{CSharp}`Nat`を次のように定義できる。
```CSharp
abstract class Nat {}
class Zero : Nat {}
class Succ : Nat {
    public Nat n;
    public Succ(Nat pred) {
        n = pred;
    }
}
```
先ほどの{anchorName Bool}`Bool`の例と同じく、これもLeanの対応する定義より多くの型を定義する。
さらにこの例は、Leanのデータ型のコンストラクタが、C#やJavaのコンストラクタというより抽象クラスのサブクラスに近いことをよく示している。ここに示したコンストラクタには、実行すべき初期化のコードが入っているからである。

直和型は、TypeScriptで文字列のタグを使って判別可能な共用体を表すのにも似ている。
TypeScriptでは、{typescript}`Nat`を次のように定義できる。
```typescript
interface Zero {
    tag: "zero";
}

interface Succ {
    tag: "succ";
    predecessor: Nat;
}

type Nat = Zero | Succ;
```
C#やJavaと同じく、この表現でもLeanより型が多くなる。{typescript}`Zero`と{typescript}`Succ`がそれぞれ独立した型だからである。
また、Leanのコンストラクタが、中身を識別するタグを持つJavaScriptやTypeScriptのオブジェクトに相当することも分かる。

# パターンマッチング
%%%
tag := "pattern-matching"
%%%

多くの言語では、この種のデータは、受け取ったのがどのサブクラスかをinstance-of演算子で調べ、そのサブクラスで使えるフィールドの値を読む、という形で扱う。
instance-ofによる確認でどのコードを実行するかが決まり、そのコードが必要とするデータが使えることが保証される。フィールドがデータそのものを与える。
Leanでは、この二つの役割を*パターンマッチング*が同時に担う。

パターンマッチングを使う関数の例が{anchorName isZero}`isZero`である。引数が{anchorName isZero}`Nat.zero`なら{anchorName isZero}`true`を返し、そうでなければfalseを返す関数である。

```anchor isZero
def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => false
```

{kw}`match`式には、分解の対象として関数の引数{anchorName isZero}`n`を渡す。
{anchorName isZero}`n`が{anchorName isZero}`Nat.zero`で作られていれば、パターンマッチングの最初の枝が選ばれ、結果は{anchorName isZero}`true`になる。
{anchorName isZero}`n`が{anchorName isZero}`Nat.succ`で作られていれば、二番目の枝が選ばれ、結果は{anchorName isZero}`false`になる。

:::paragraph
{anchorEvalStep isZeroZeroSteps 0}`isZero Nat.zero`の評価は、次のように一歩ずつ進む。

```anchorEvalSteps  isZeroZeroSteps
isZero Nat.zero
===>
match Nat.zero with
| Nat.zero => true
| Nat.succ k => false
===>
true
```
:::

:::paragraph
{anchorEvalStep isZeroFiveSteps 0}`isZero 5`の評価も同様に進む。

```anchorEvalSteps  isZeroFiveSteps
isZero 5
===>
isZero (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))
===>
match Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) with
| Nat.zero => true
| Nat.succ k => false
===>
false
```
:::

{anchorName isZero}`isZero`のパターンの二番目の枝にある{anchorName isZero}`k`は飾りではない。
{anchorName isZero}`Nat.succ`の引数である{anchorName isZero}`Nat`に、与えた名前を付けて見えるようにする。
そうして取り出した小さい方の数を使って、式の最終的な結果を計算できる。


:::paragraph
ある数$`n`の後者が$`n`より1大きい（つまり$`n + 1`）のと同じように、ある数の前者はその数より1小さい。
{anchorName pred}`Nat`の前者を求める関数が{anchorName pred}`pred`なら、次の例は期待どおりの結果になるはずである。

```anchor  predFive
#eval pred 5
```

```anchorInfo predFive
4
```

```anchor predBig
#eval pred 839
```

```anchorInfo predBig
838
```
:::

:::paragraph
{anchorName Nat}`Nat`は負の数を表せないので、{anchorName NatNames}`Nat.zero`の扱いは少し厄介である。
{anchorName Nat}`Nat`を扱うときは通常、負の数になるはずの演算子を、{anchorName NatNames}`zero`を返すように定義し直す。

```anchor predZero
#eval pred 0
```
```anchorInfo predZero
0
```
:::


{anchorName pred}`Nat`の前者を求めるには、まずどのコンストラクタで作られたかを調べる。
{anchorName pred}`Nat.zero`なら、結果は{anchorName pred}`Nat.zero`である。
{anchorName pred}`Nat.succ`なら、その下にある{anchorName plus}`Nat`を{anchorName pred}`k`という名前で指す。
この{anchorName pred}`Nat`が求める前者なので、{anchorName pred}`Nat.succ`の枝の結果は{anchorName pred}`k`である。

```anchor pred
def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k
```

:::paragraph
この関数を{anchorTerm predFiveSteps}`5`に適用すると、次のように進む。

```anchorEvalSteps  predFiveSteps
pred 5
===>
pred (Nat.succ 4)
===>
match Nat.succ 4 with
| Nat.zero => Nat.zero
| Nat.succ k => k
===>
4
```
:::

:::paragraph
パターンマッチングは、直和型だけでなく構造体にも使える。
たとえば、{anchorName depth}`Point3D`から三次元目の値を取り出す関数は次のように書ける。

```anchor depth
def depth (p : Point3D) : Float :=
  match p with
  | { x:= h, y := w, z := d } => d
```

この場合は{anchorName fragments}`Point3D.z`アクセサを使う方がずっと簡単だが、構造体のパターンが関数を書く最も簡単な方法になることもある。
:::

# 再帰関数
%%%
tag := "recursive-functions"
%%%

定義しようとしている名前自身を参照する定義を*再帰的定義*と呼ぶ。
帰納的データ型は再帰的であってよい。{anchorName Nat}`succ`が別の{anchorName Nat}`Nat`を要求するので、{anchorName Nat}`Nat`はその例である。
再帰的データ型はいくらでも大きなデータを表せる。制限になるのは、利用できるメモリのような技術的な要因だけである。
データ型の定義に自然数一つずつに対応するコンストラクタを書けないのと同じように、パターンマッチングの枝を可能性ごとに書くこともできない。

:::paragraph
再帰的データ型には再帰関数がよく合う。
{anchorName even}`Nat`に対する簡単な再帰関数として、引数が偶数かどうかを調べるものがある。
この場合、{anchorName even}`Nat.zero`は偶数である。
このような再帰しない枝を*基底ケース*と呼ぶ。
奇数の後者は偶数であり、偶数の後者は奇数である。
つまり、{anchorName even}`Nat.succ`で作られた数が偶数であるのは、その引数が偶数でないとき、かつそのときに限る。

```anchor even
def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)
```

:::


{anchorName even}`Nat`に対する再帰関数を書くときは、たいていこの考え方をする。
まず{anchorName even}`Nat.zero`の場合に何をするかを決める。
次に、任意の{anchorName even}`Nat`についての結果を、その後者についての結果に変換する方法を決め、その変換を再帰呼び出しの結果に適用する。
この形を*構造的再帰*と呼ぶ。

:::paragraph
多くの言語と違い、Leanは既定で、すべての再帰関数が最終的に基底ケースに到達することを保証する。
プログラミングの観点では、これによってうっかり無限ループになることを防げる。
この性質は、無限ループが大きな問題を引き起こす定理の証明ではとくに重要である。
その結果、元の数に対して自分自身を再帰的に呼び出そうとする{anchorName even}`even`はLeanに受け入れられない。

```anchor evenLoops
def evenLoops (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (evenLoops n)
```
このエラーメッセージの要点は、Leanがこの再帰関数について常に基底ケースに到達することを示せなかったという点である（実際に到達しない）。

```anchorError evenLoops
fail to show termination for
  evenLoops
with errors
failed to infer structural recursion:
Not considering parameter n of evenLoops:
  it is unchanged in the recursive calls
no parameters suitable for structural recursion

well-founded recursion cannot be used, `evenLoops` does not take any (non-fixed) arguments
```

:::

:::paragraph
加法は二つの引数を取るが、調べる必要があるのはそのうちの一つだけである。
数$`n`に0を足すには、$`n`をそのまま返す。
$`n`に$`k`の後者を足すには、$`n`に$`k`を足した結果の後者を取る。

```anchor plus
def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')
```

:::

:::paragraph
{anchorName plus}`plus`の定義で{anchorName plus}`k'`という名前を選んだのは、引数{anchorName plus}`k`と関係はあるが同一ではないことを示すためである。
たとえば、{anchorEvalStep plusThreeTwo 0}`plus 3 2`の評価をたどると、次のようになる。

```anchorEvalSteps  plusThreeTwo
plus 3 2
===>
plus 3 (Nat.succ (Nat.succ Nat.zero))
===>
match Nat.succ (Nat.succ Nat.zero) with
| Nat.zero => 3
| Nat.succ k' => Nat.succ (plus 3 k')
===>
Nat.succ (plus 3 (Nat.succ Nat.zero))
===>
Nat.succ (match Nat.succ Nat.zero with
| Nat.zero => 3
| Nat.succ k' => Nat.succ (plus 3 k'))
===>
Nat.succ (Nat.succ (plus 3 Nat.zero))
===>
Nat.succ (Nat.succ (match Nat.zero with
| Nat.zero => 3
| Nat.succ k' => Nat.succ (plus 3 k')))
===>
Nat.succ (Nat.succ 3)
===>
5
```
:::

:::paragraph
加法は、$`n + k`が$`n`に{anchorName times}`Nat.succ`を$`k`回適用するものだと考えることもできる。
同様に、乗算$`n × k`は$`n`を$`k`回足し合わせるものであり、減算$`n - k`は$`n`の前者を$`k`回取るものである。

```anchor times
def times (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (times n k')
```

```anchor minus
def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => pred (minus n k')
```

:::

:::paragraph
すべての関数が構造的再帰で簡単に書けるわけではない。
加法を{anchorName plus}`Nat.succ`の繰り返し、乗算を加法の繰り返し、減算を前者を取る操作の繰り返しと捉えるなら、除算は減算の繰り返しとして実装できそうである。
この場合、分子が除数より小さければ結果は0である。
そうでなければ、分子から除数を引いたものを除数で割った結果の後者が結果になる。

```anchor div
def div (n : Nat) (k : Nat) : Nat :=
  if n < k then
    0
  else Nat.succ (div (n - k) k)
```
:::

:::paragraph
二番目の引数が{anchorTerm div}`0`でない限り、このプログラムは停止する。常に基底ケースに近づくためである。
しかし、この定義は構造的再帰ではない。0の場合の結果を決め、より小さい{anchorName div}`Nat`についての結果をその後者の結果に変換する、という形になっていないためである。
とくに、この関数の再帰呼び出しは、入力のコンストラクタの引数ではなく、別の関数呼び出しの結果に対して行われている。
そのため、Leanは次のメッセージを出して受け付けない。

```anchorError div
fail to show termination for
  div
with errors
failed to infer structural recursion:
Not considering parameter k of div:
  it is unchanged in the recursive calls
Cannot use parameter n:
  failed to eliminate recursive application
    div (n - k) k


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
k n : Nat
h✝ : ¬n < k
⊢ n - k < n
```

このメッセージは、{anchorName div}`div`には停止性の証明を自分で与える必要がある、という意味である。
この話題は{ref "division-as-iterated-subtraction"}[最終章]で扱う。
:::
