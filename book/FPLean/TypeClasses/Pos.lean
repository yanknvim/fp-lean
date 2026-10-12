module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true

#doc (Manual) "Positive Numbers" =>
%%%
tag := "positive-numbers"
%%%

アプリケーションによっては、正の数しか意味をなさないことがある。
たとえば、コンパイラやインタプリタは通常、ソース上の位置に行番号と列番号を1始まりで使うし、空でないリストだけを表すデータ型が長さ0を返すことはない。
自然数に頼り、0でないことを確かめる検査をコードのあちこちに散らすより、正の数だけを表すデータ型を設計した方が役に立つことがある。

正の数を表す一つの方法は、基底ケースを{anchorTerm Nat.zero}`zero`ではなく{anchorTerm Pos}`one`にするだけで、{anchorTerm chapterIntro}`Nat`とよく似ている。

```anchor Pos
inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos
```
このデータ型は意図した値の集合をちょうど表すが、使い勝手はよくない。
たとえば、数値リテラルは受け付けられない。
```anchor sevenOops
def seven : Pos := 7
```
```anchorError sevenOops
failed to synthesize instance of type class
  OfNat Pos 7
numerals are polymorphic in Lean, but the numeral `7` cannot be used in a context where the expected type is
  Pos
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
代わりに、コンストラクタを直接使わなければならない。
```anchor seven
def seven : Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))
```

同様に、加法と乗法も使いにくい。
```anchor fourteenOops
def fourteen : Pos := seven + seven
```
```anchorError fourteenOops
failed to synthesize instance of type class
  HAdd Pos Pos ?m.3

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
```anchor fortyNineOops
def fortyNine : Pos := seven * seven
```
```anchorError fortyNineOops
failed to synthesize instance of type class
  HMul Pos Pos ?m.3

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

どのエラーメッセージも{lit}`failed to synthesize`で始まっている。
これは、実装されていないオーバーロードされた操作が原因のエラーであることを示し、実装すべき型クラスを述べている。

# クラスとインスタンス
%%%
tag := "classes-and-instances"
%%%

型クラスは、名前、いくつかの引数、{deftech}*メソッド*の集まりから成る。
引数は、オーバーロードできる操作を定義する対象の型を記述し、メソッドはその操作の名前と型シグネチャである。
ここでも、オブジェクト指向言語との用語の衝突がある。
オブジェクト指向プログラミングでは、メソッドは本質的に、メモリ上の特定のオブジェクトに結び付いた関数であり、そのオブジェクトの非公開の状態に特別にアクセスできる。
オブジェクトとはメソッドを通じてやり取りする。
Leanでは、「メソッド」という語は、オーバーロード可能として宣言された操作を指し、オブジェクトや値、非公開のフィールドとは特別な関係がない。

加法をオーバーロードする一つの方法は、{anchorName Plus}`Plus`という型クラスを定義し、{anchorName Plus}`plus`という加法のメソッドを持たせることである。
{anchorTerm chapterIntro}`Nat`に対する{anchorTerm Plus}`Plus`のインスタンスを定義すると、{anchorName plusNatFiveThree}`Plus.plus`を使って二つの{anchorTerm chapterIntro}`Nat`を足せるようになる。
```anchor plusNatFiveThree
#eval Plus.plus 5 3
```
```anchorInfo plusNatFiveThree
8
```
インスタンスを増やせば、{anchorName plusNatFiveThree}`Plus.plus`がより多くの型の引数を取れるようになる。

次の型クラスの宣言では、{anchorName Plus}`Plus`がクラスの名前、{anchorTerm Plus}`α : Type`が唯一の引数、{anchorTerm Plus}`plus : α → α → α`が唯一のメソッドである。

```anchor Plus
class Plus (α : Type) where
  plus : α → α → α
```
この宣言は、型{anchorName Plus}`α`について操作をオーバーロードする{anchorName Plus}`Plus`という型クラスがある、と述べている。
とくに、{anchorName Plus}`α`を二つ取り{anchorName Plus}`α`を返す{anchorName Plus}`plus`というオーバーロードされた操作が一つある。

型が第一級であるのと同じく、型クラスも第一級である。
とくに、型クラスもまた一種の型である。
{anchorTerm PlusType}`Plus`の型は{anchorTerm PlusType}`Type → Type`である。{anchorName Plus}`α`という型を引数に取り、{anchorName Plus}`Plus`の操作を{anchorName Plus}`α`についてオーバーロードすることを記述する新しい型を結果として生むためである。


特定の型に対して{anchorName PlusNat}`plus`をオーバーロードするには、インスタンスを書く。

```anchor PlusNat
instance : Plus Nat where
  plus := Nat.add
```
{anchorTerm PlusNat}`instance`の後ろのコロンは、{anchorTerm PlusNat}`Plus Nat`が確かに型であることを示す。
クラス{anchorName Plus}`Plus`の各メソッドには、{anchorTerm PlusNat}`:=`を使って値を割り当てる。
ここではメソッドは{anchorName PlusNat}`plus`の一つだけである。

既定では、型クラスのメソッドは型クラスと同じ名前の名前空間に定義される。
その名前空間を{anchorTerm openPlus}`open`しておくと、利用者がクラス名を先に打たなくて済むので便利なことがある。
{kw}`open`コマンドの括弧は、その名前空間から指定した名前だけを使えるようにする、という意味である。

```anchor openPlus
open Plus (plus)
```
```anchor plusNatFiveThreeAgain
#eval plus 5 3
```
```anchorInfo plusNatFiveThreeAgain
8
```

{anchorName PlusPos}`Pos`に対する加法の関数と{anchorTerm PlusPos}`Plus Pos`のインスタンスを定義すれば、{anchorName PlusPos}`plus`で{anchorName PlusPos}`Pos`の値も{anchorTerm chapterIntro}`Nat`の値も足せるようになる。

```anchor PlusPos
def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

instance : Plus Pos where
  plus := Pos.plus

def fourteen : Pos := plus seven seven
```

まだ{anchorTerm PlusFloat}`Plus Float`のインスタンスがないので、{anchorName plusFloatFail}`plus`で二つの浮動小数点数を足そうとすると、見覚えのあるメッセージを伴って失敗する。
```anchor plusFloatFail
#eval plus 5.2 917.25861
```
```anchorError plusFloatFail
failed to synthesize instance of type class
  Plus Float

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
これらのエラーは、Leanがその型クラスのインスタンスを見つけられなかったという意味である。

# 加法のオーバーロード
%%%
tag := "overloaded-addition"
%%%

Leanの組み込みの加法演算子は、{anchorName chapterIntro}`HAdd`という型クラスの構文糖である。{anchorName chapterIntro}`HAdd`は、加法の引数が異なる型でもよいように柔軟にできている。
{anchorName chapterIntro}`HAdd`は*異種の加法*（heterogeneous addition）の略である。
たとえば、{anchorName chapterIntro}`Nat`と{anchorName fiveZeros}`Float`を足して新しい{anchorName fiveZeros}`Float`にする{anchorName chapterIntro}`HAdd`のインスタンスを書ける。
プログラマが{anchorTerm plusDesugar}`x + y`と書くと、{anchorTerm plusDesugar}`HAdd.hAdd x y`という意味として解釈される。

{anchorName chapterIntro}`HAdd`の完全な一般性を理解するには{ref "out-params"}[この章の別の節]で扱う機能が必要だが、引数の型を混ぜられない、より単純な{anchorName AddPos}`Add`という型クラスもある。
Leanのライブラリは、両方の引数が同じ型である{anchorName chapterIntro}`HAdd`のインスタンスを探すときに、{anchorName AddPos}`Add`のインスタンスが見つかるようにできている。

{anchorTerm AddPos}`Add Pos`のインスタンスを定義すると、{anchorTerm AddPos}`Pos`の値で普通の加法の記法を使える。

```anchor AddPos
instance : Add Pos where
  add := Pos.plus
```
```anchor betterFourteen
def fourteen : Pos := seven + seven
```

# 文字列への変換
%%%
tag := "conversion-to-strings"
%%%

もう一つの便利な組み込みのクラスが{anchorName UglyToStringPos}`ToString`である。
{anchorName UglyToStringPos}`ToString`のインスタンスは、与えられた型の値を文字列に変換する標準的な方法を与える。
たとえば、値が補間された文字列の中にあるときに{anchorName UglyToStringPos}`ToString`のインスタンスが使われ、{ref "running-a-program"}[{anchorName readFile}`IO`の説明の冒頭]で使った{anchorName printlnType}`IO.println`が値をどう表示するかもこれで決まる。

たとえば、{anchorName Pos}`Pos`を{anchorName readFile}`String`に変換する一つの方法は、その内部構造をそのまま見せることである。
関数{anchorName posToStringStructure}`posToString`は、{anchorName posToStringStructure}`Pos.succ`の使用に括弧を付けるかどうかを決める{anchorName posToStringStructure}`Bool`を取り、最初の呼び出しでは{anchorName CoeBoolProp}`true`、再帰呼び出しではすべて{anchorName posToStringStructure}`false`にする。

```anchor posToStringStructure
def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"
```
この関数を{anchorName UglyToStringPos}`ToString`のインスタンスに使うと、

```anchor UglyToStringPos
instance : ToString Pos where
  toString := posToString true
```
情報量はあるが圧倒される出力になる。
```anchor sevenLong
#eval s!"There are {seven}"
```
```anchorInfo sevenLong
"There are Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))"
```

一方、すべての正の数には対応する{anchorTerm chapterIntro}`Nat`がある。
それを{anchorTerm chapterIntro}`Nat`に変換し、{anchorTerm chapterIntro}`ToString Nat`のインスタンス（つまり{anchorTerm chapterIntro}`Nat`に対する{anchorName UglyToStringPos}`ToString`のオーバーロード）を使えば、ずっと短い出力を簡単に得られる。

```anchor posToNat
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1
```
```anchor PosToStringNat
instance : ToString Pos where
  toString x := toString (x.toNat)
```
```anchor sevenShort
#eval s!"There are {seven}"
```
```anchorInfo sevenShort
"There are 7"
```
二つ以上のインスタンスを定義した場合、最後に定義したものが優先される。
さらに、ある型に{anchorName UglyToStringPos}`ToString`のインスタンスがあれば、{kw}`#eval`の結果の表示にも使われるので、{anchorTerm sevenEvalStr}`#eval seven`は{anchorInfo sevenEvalStr}`7`を出力する。

# 乗法のオーバーロード
%%%
tag := "overloaded-multiplication"
%%%

乗法にも、{anchorName chapterIntro}`HAdd`と同じく引数の型を混ぜられる{anchorName MulPPoint}`HMul`という型クラスがある。
{anchorTerm plusDesugar}`x + y`が{anchorTerm plusDesugar}[`HAdd.hAdd x y`]と解釈されるのと同じように、{anchorTerm timesDesugar}`x * y`は{anchorTerm timesDesugar}`HMul.hMul x y`と解釈される。
同じ型の二つの引数の乗法というよくある場合は、{anchorName PosMul}`Mul`のインスタンスで足りる。

{anchorTerm PosMul}`Mul`のインスタンスを定義すると、{anchorName PosMul}`Pos`で普通の乗法の記法を使える。

```anchor PosMul
def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k

instance : Mul Pos where
  mul := Pos.mul
```
このインスタンスにより、乗法は期待どおりに働く。
```anchor muls
#eval [seven * Pos.one,
       seven * seven,
       Pos.succ Pos.one * seven]
```
```anchorInfo muls
[7, 49, 14]
```

# 数値リテラル
%%%
tag := "literal-numbers"
%%%

正の数のためにコンストラクタの並びを書き下すのは、かなり不便である。
この問題を避ける方法の一つは、{anchorTerm chapterIntro}`Nat`を{anchorName Pos}`Pos`に変換する関数を用意することである。
ただし、この方法には難点がある。
第一に、{anchorName PosMul}`Pos`は{anchorTerm nats}`0`を表せないので、その関数は{anchorTerm chapterIntro}`Nat`をより大きな数に変換するか、{anchorTerm PosStuff}`Option Pos`を返すかのどちらかになる。
どちらも利用者にとって特に便利とは言えない。
第二に、関数を明示的に呼ばなければならないと、正の数を使うプログラムは{anchorTerm chapterIntro}`Nat`を使うプログラムよりずっと書きにくくなる。
正確な型と便利なAPIのどちらかを選ばなければならないとなると、正確な型は役に立ちにくくなる。

数値リテラルのオーバーロードに使う型クラスは三つある。{anchorName Zero}`Zero`、{anchorName One}`One`、{anchorName OfNat}`OfNat`である。
多くの型が{anchorTerm nats}`0`で自然に書ける値を持つので、{anchorName Zero}`Zero`クラスはその特定の値を差し替えられるようにする。
定義は次のとおりである。

```anchor Zero
class Zero (α : Type) where
  zero : α
```
{anchorTerm nats}`0`は正の数ではないので、{anchorTerm PosStuff}`Zero Pos`のインスタンスはないはずである。

同様に、多くの型が{anchorTerm nats}`1`で自然に書ける値を持つ。
{anchorName One}`One`クラスはそれを差し替えられるようにする。
```anchor One
class One (α : Type) where
  one : α
```
{anchorTerm OnePos}`One Pos`のインスタンスは十分に意味がある。
```anchor OnePos
instance : One Pos where
  one := Pos.one
```
このインスタンスにより、{anchorTerm OnePos}`Pos.one`の代わりに{anchorTerm onePos}`1`を使える。
```anchor onePos
#eval (1 : Pos)
```
```anchorInfo onePos
1
```

Leanでは、自然数のリテラルは{anchorName OfNat}`OfNat`という型クラスを使って解釈される。

```anchor OfNat
class OfNat (α : Type) (_ : Nat) where
  ofNat : α
```
この型クラスは二つの引数を取る。{anchorTerm OfNat}`α`は自然数をオーバーロードする対象の型であり、名前のない{anchorTerm chapterIntro}`Nat`の引数は、プログラム中に現れた実際のリテラルの数である。
メソッド{anchorName OfNat}`ofNat`が、その数値リテラルの値として使われる。
クラスが{anchorTerm chapterIntro}`Nat`の引数を含むので、その数が意味を持つ値についてだけインスタンスを定義できる。

{anchorTerm OfNat}`OfNat`は、型クラスの引数が型である必要はないことを示している。
Leanでは型が言語の第一級の要素であり、関数の引数として渡せ、{kw}`def`や{kw}`abbrev`で定義を与えられるので、融通の利かない言語では許されない位置に型以外の引数を置くことを妨げる障壁がない。
この柔軟さにより、特定の型だけでなく特定の値についてもオーバーロードされた操作を用意できる。
さらに、{anchorTerm ListSum}`OfNat α 0`のインスタンスがあれば必ず{anchorTerm ListSumZ}`Zero α`のインスタンスがある、という関係をLeanの標準ライブラリが整えられる。その逆も同様である。
同様に、{anchorTerm OneExamples}`One α`のインスタンスは{anchorTerm OneExamples}`OfNat α 1`のインスタンスを導き、{anchorTerm OneExamples}`OfNat α 1`のインスタンスは{anchorTerm OneExamples}`One α`のインスタンスを導く。

4未満の自然数を表す直和型は次のように定義できる。

```anchor LT4
inductive LT4 where
  | zero
  | one
  | two
  | three
```
この型に*どんな*数値リテラルでも使えるのは意味をなさないが、4未満の数なら明らかに意味がある。

```anchor LT4ofNat
instance : OfNat LT4 0 where
  ofNat := LT4.zero

instance : OfNat LT4 1 where
  ofNat := LT4.one

instance : OfNat LT4 2 where
  ofNat := LT4.two

instance : OfNat LT4 3 where
  ofNat := LT4.three
```
これらのインスタンスにより、次の例は動作する。
```anchor LT4three
#eval (3 : LT4)
```
```anchorInfo LT4three
LT4.three
```
```anchor LT4zero
#eval (0 : LT4)
```
```anchorInfo LT4zero
LT4.zero
```
一方、範囲外のリテラルは依然として許されない。
```anchor LT4four
#eval (4 : LT4)
```
```anchorError LT4four
failed to synthesize instance of type class
  OfNat LT4 4
numerals are polymorphic in Lean, but the numeral `4` cannot be used in a context where the expected type is
  LT4
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

{anchorName PosMul}`Pos`では、{anchorTerm OfNat}`OfNat`のインスタンスは{anchorName PosStuff}`Nat.zero`以外の*任意の*{anchorTerm chapterIntro}`Nat`に対して働くべきである。
言い換えれば、すべての自然数{anchorTerm posrec}`n`について、インスタンスが{anchorTerm posrec}`n + 1`に対して働くべきである。
{anchorTerm posrec}`α`のような名前が自動的に暗瞑の引数になり、Leanが自分で補うのと同じように、インスタンスも自動的な暗瞑の引数を取れる。
このインスタンスでは、引数{anchorTerm OfNatPos}`n`が任意の{anchorTerm chapterIntro}`Nat`を表し、その1だけ大きい{anchorTerm chapterIntro}`Nat`に対してインスタンスが定義される。

```anchor OfNatPos
instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n
```
{anchorTerm OfNatPos}`n`は利用者が書いた数より1小さい{anchorTerm chapterIntro}`Nat`を表すので、補助関数{anchorName OfNatPos}`natPlusOne`は引数より1大きい{anchorName OfNatPos}`Pos`を返す。
これにより、正の数には自然数のリテラルを使えるが、0には使えない。

```anchor eight
def eight : Pos := 8
```
```anchor zeroBad
def zero : Pos := 0
```
```anchorError zeroBad
failed to synthesize instance of type class
  OfNat Pos 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  Pos
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

# 練習問題
%%%
tag := "positive-numbers-exercises"
%%%

## 別の表現
%%%
tag := "positive-numbers-another-representation"
%%%

正の数を表す別の方法は、ある{anchorTerm chapterIntro}`Nat`の後者として表すものである。
{anchorName PosStuff}`Pos`の定義を、{anchorTerm chapterIntro}`Nat`を入れる{anchorName AltPos}`succ`という名前のコンストラクタを持つ構造体で置き換えよ。

```anchor AltPos
structure Pos where
  succ ::
  pred : Nat
```
この版の{anchorName AltPos}`Pos`を便利に使えるようにする{moduleName}`Add`、{moduleName}`Mul`、{anchorName UglyToStringPos}`ToString`、{moduleName}`OfNat`のインスタンスを定義せよ。

## 偶数
%%%
tag := "even-numbers-ex"
%%%

偶数だけを表すデータ型を定義せよ。それを便利に使えるようにする{moduleName}`Add`、{moduleName}`Mul`、{anchorName UglyToStringPos}`ToString`のインスタンスを定義せよ。
{moduleName}`OfNat`には{ref "tc-polymorphism"}[次の節]で導入する機能が必要である。

## HTTPリクエスト
%%%
tag := "http-request-ex"
%%%

HTTPリクエストは、{lit}`GET`や{lit}`POST`のようなHTTPメソッドの指定と、URI、HTTPのバージョンから始まる。
HTTPメソッドのうち興味深い部分集合を表す帰納型と、HTTPレスポンスを表す構造体を定義せよ。
レスポンスには、デバッグできるようにする{anchorName UglyToStringPos}`ToString`のインスタンスを持たせる。
型クラスを使って各HTTPメソッドに異なる{moduleName}`IO`アクションを対応付け、各メソッドを呼び出して結果を表示する{moduleName}`IO`アクションとしてテスト用の仕組みを書け。
