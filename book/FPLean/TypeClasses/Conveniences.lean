module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true


#doc (Manual) "Additional Conveniences" =>
%%%
tag := "type-class-conveniences"
%%%

# インスタンスのコンストラクタ記法
%%%
tag := "instance-constructor-syntax"
%%%

舞台裏では、型クラスは構造体型であり、インスタンスはその型の値である。
違いは、Leanが型クラスについて追加の情報（どの引数が出力パラメータか、など）を保存することと、インスタンスが検索用に登録されることだけである。
構造体型の値は通常{lit}`⟨...⟩`の記法か、淡括弧とフィールドで定義し、インスタンスは通常{kw}`where`で定義するが、どちらの記法もどちらの種類の定義にも使える。

:::paragraph
たとえば、林業のアプリケーションで木を次のように表すとする。

```anchor trees
structure Tree : Type where
  latinName : String
  commonNames : List String

def oak : Tree :=
  ⟨"Quercus robur", ["common oak", "European oak"]⟩

def birch : Tree :=
  { latinName := "Betula pendula",
    commonNames := ["silver birch", "warty birch"]
  }

def sloe : Tree where
  latinName := "Prunus spinosa"
  commonNames := ["sloe", "blackthorn"]
```
三つの記法はすべて同等である。
:::

:::paragraph
同様に、型クラスのインスタンスも三つの記法すべてで定義できる。

```anchor Display
class Display (α : Type) where
  displayName : α → String

instance : Display Tree :=
  ⟨Tree.latinName⟩

instance : Display Tree :=
  { displayName := Tree.latinName }

instance : Display Tree where
  displayName t := t.latinName
```

{kw}`where`の記法は通常インスタンスに使い、構造体には淡括弧の記法か{kw}`where`の記法を使う。
{lit}`⟨...⟩`の記法は、構造体型が、たまたまフィールドに名前が付いたタプルのようなものであり、今はその名前が重要でない、という点を強調したいときに役に立つ。
ただし、別の書き方を使う方が妥当な場面もある。
とくに、ライブラリがインスタンスの値を作る関数を提供していることがある。
インスタンスの宣言で{lit}`:=`の後にその関数の呼び出しを置くのが、そうした関数を使う最も簡単な方法である。
:::

# example宣言
%%%
tag := "example-command"
%%%

Leanのコードを試すときには、{kw}`#eval`や{kw}`#check`のコマンドより定義の方が便利なことがある。
第一に、定義は何も出力しないので、読み手の注意を本当に見たい出力に保ちやすい。
第二に、ほとんどのLeanのプログラムは型シグネチャから書き始めるのが最も楽であり、そうすればプログラムを書いている間にLeanからより多くの支援と良いエラーメッセージが得られる。
一方、{kw}`#eval`や{kw}`#check`は、与えられた式からLeanが型を決められる場面で最も使いやすい。
第三に、{kw}`#eval`は、型に{moduleName}`ToString`や{moduleName}`Repr`のインスタンスがない式（関数など）には使えない。
最後に、複数手順の{kw}`do`ブロックや{kw}`let`式など、複数行にわたる構文は、{kw}`#eval`や{kw}`#check`に型注釈を付けて書くのがとくに難しい。必要な括弧の付け方を予想しにくいためである。

:::paragraph
これらの問題を避けるために、Leanはソースファイル中で例を明示できるようにしている。
exampleは、名前のない定義のようなものである。
たとえば、コペンハーゲンの緑地でよく見られる鳥の空でないリストは次のように書ける。

```anchor birdExample
example : NonEmptyList String :=
  { head := "Sparrow",
    tail := ["Duck", "Swan", "Magpie", "Eurasian coot", "Crow"]
  }
```
:::

:::paragraph
exampleは引数を受け取って関数を定義することもできる。

```anchor commAdd
example (n : Nat) (k : Nat) : Bool :=
  n + k == k + n
```
舞台裏では関数が作られるが、その関数には名前がなく、呼び出せない。
それでも、ある型の任意の値や未知の値に対してライブラリをどう使えるかを示すのに役に立つ。
ソースファイルでは、{kw}`example`の宣言には、その例がライブラリの概念をどう示しているかを説明するコメントを添えるのがよい。
:::
