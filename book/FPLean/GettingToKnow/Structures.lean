module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

example_module Examples.Intro

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"

#doc (Manual) "Structures" =>
%%%
tag := "structures"
%%%

プログラムを書くときの最初の一歩は、たいてい、対象とする問題領域の概念を見つけ出し、それをコードでどう表すかを決めることである。
ある概念が、いくつかのより単純な概念の集まりであることもある。
そのような場合は、単純な部品を一つの「まとまり」にまとめ、意味のある名前を付けておくと便利である。
Leanではこれを*構造体*で行う。CやRustの{c}`struct`、C#の{CSharp}`record`に相当する。

構造体を定義すると、他のどの型にも還元できない新しい型がLeanに導入される。
複数の構造体が、同じデータを持ちながら別の概念を表すことがあるため、これは役に立つ。
たとえば点は、直交座標でも極座標でも表せる。どちらも浮動小数点数の組である。
別々の構造体として定義しておけば、APIの利用者が両者を取り違えることを防げる。

Leanの浮動小数点数の型は{anchorName zeroFloat}`Float`といい、普通の表記で書ける。

```anchorTerm onePointTwo
#check 1.2
```


```anchorInfo onePointTwo
1.2 : Float
```


```anchorTerm negativeLots
#check -454.2123215
```


```anchorInfo negativeLots
-454.2123215 : Float
```


```anchorTerm zeroPointZero
#check 0.0
```


```anchorInfo zeroPointZero
0.0 : Float
```

小数点を付けて書いた浮動小数点数なら、Leanは型を{anchorName zeroFloat}`Float`と推論する。小数点を付けない場合は、型注釈が必要になることがある。

```anchorTerm zeroNat
#check 0
```


```anchorInfo zeroNat
0 : Nat
```



```anchorTerm zeroFloat
#check (0 : Float)
```


```anchorInfo zeroFloat
0 : Float
```



直交座標の点は、{anchorName Point}`x`と{anchorName Point}`y`という二つの{anchorName zeroFloat}`Float`のフィールドを持つ構造体である。
これは{kw}`structure`キーワードで宣言する。


```anchor Point
structure Point where
  x : Float
  y : Float
```

この宣言により、{anchorName Point}`Point`という新しい構造体の型ができる。
構造体の型の値を作るには、淡括弧の中にすべてのフィールドの値を書くのが普通である。
直交座標平面の原点は、{anchorName Point}`x`と{anchorName Point}`y`がどちらも0である点である。

```anchor origin
def origin : Point := { x := 0.0, y := 0.0 }
```

{anchorTerm originEval}`#eval origin`の結果は、{anchorName origin}`origin`の定義とよく似ている。

```anchorInfo originEval
{ x := 0.000000, y := 0.000000 }
```


構造体は、データの集まりを一つにまとめ、名前を付けて一つの単位として扱うためのものなので、個々のフィールドを取り出せることも重要である。
取り出しには、C、Python、Rust、JavaScriptと同じようにドット記法を使う。

```anchorTerm originx
#eval origin.x
```

```anchorInfo originx
0.000000
```


```anchorTerm originy
#eval origin.y
```

```anchorInfo originy
0.000000
```

:::paragraph
これを使って、構造体を引数に取る関数を定義できる。
たとえば、点の足し算は、対応する座標の値を足し合わせて行う。
次のようになるはずである。

```anchorTerm addPointsEx
#eval addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 }
```

これは次のようになる。

```anchorInfo addPointsEx
{ x := -6.500000, y := 32.200000 }
```
:::

この関数は二つの{anchorName Point}`Point`を引数に取り、それぞれ{anchorName addPoints}`p1`と{anchorName addPoints}`p2`と呼ぶ。
結果の点は、{anchorName addPoints}`p1`と{anchorName addPoints}`p2`の{anchorName addPoints}`x`と{anchorName addPoints}`y`の各フィールドから作られる。

```anchor addPoints
def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }
```


同様に、二点間の距離（それぞれの{anchorName Point}`x`と{anchorName Point}`y`の差を二乗して足し、平方根を取ったもの）は次のように書ける。

```anchor distance
def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))
```

たとえば$`(1, 2)`と$`(5, -1)`の距離は$`5`である。

```anchorTerm evalDistance
#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }
```

```anchorInfo evalDistance
5.000000
```



複数の構造体が同じ名前のフィールドを持つこともある。
三次元の点を表すデータ型が{anchorName Point3D}`x`と{anchorName Point3D}`y`というフィールドを共有し、同じフィールド名で値を作ることもある。

```anchor Point3D
structure Point3D where
  x : Float
  y : Float
  z : Float
```

```anchor origin3D
def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }
```

つまり、淡括弧の記法を使うには、どの構造体の型なのかが分かっていなければならない。
型が分からないと、Leanは構造体の値を組み立てられない。
たとえば、

```anchorTerm originNoType
#check { x := 0.0, y := 0.0 }
```

とすると、次のエラーになる。

```anchorError originNoType
invalid {...} notation, expected type is not known
```


いつもどおり、型注釈を付ければ解決する。

```anchorTerm originWithAnnot
#check ({ x := 0.0, y := 0.0 } : Point)
```


```anchorInfo originWithAnnot
{ x := 0.0, y := 0.0 } : Point
```


プログラムを簡潔にするため、Leanでは淡括弧の中に構造体の型注釈を書くこともできる。

```anchorTerm originWithAnnot2
#check { x := 0.0, y := 0.0 : Point}
```


```anchorInfo originWithAnnot2
{ x := 0.0, y := 0.0 } : Point
```


# 構造体の更新
%%%
tag := "updating-structures"
%%%

{anchorName zeroXBad}`Point`の{anchorName zeroXBad}`x`フィールドを{anchorTerm zeroX}`0`に置き換える関数{anchorName zeroXBad}`zeroX`を考える。
多くのプログラミング言語の世界では、この文は{anchorName Point}`x`が指すメモリ上の場所を新しい値で上書きするという意味になる。
しかしLeanは関数型プログラミング言語である。
関数型プログラミングの世界でこの種の文がほぼ常に意味するのは、新しい{anchorName Point}`Point`を割り当て、その{anchorName Point}`x`フィールドに新しい値を指させ、他のフィールドは入力の元の値を指させる、ということである。
{anchorName zeroXBad}`zeroX`を書く一つの方法は、この説明に文字どおり従い、{anchorName Point}`x`に新しい値を書き、{anchorName Point}`y`は元の値を手で引き継ぐことである。

```anchor zeroXBad
def zeroX (p : Point) : Point :=
  { x := 0, y := p.y }
```

ただし、この書き方には難点がある。
第一に、構造体にフィールドを追加すると、どのフィールドであれ更新している箇所をすべて直さなければならず、保守が難しくなる。
第二に、同じ型のフィールドが複数あると、コピー＆ペーストによってフィールドの中身を取り違えたり重複させたりする危険が現実にある。
第三に、プログラムが長くなり、事務的になる。

Leanには、一部のフィールドだけを置き換え、残りはそのままにする便利な記法がある。
構造体の初期化で{kw}`with`キーワードを使う。
変更しないフィールドの元になる値は{kw}`with`の前に書き、新しいフィールドは後ろに書く。
たとえば{anchorName zeroX}`zeroX`は、新しい{anchorName Point}`x`の値だけで書ける。

```anchor zeroX
def zeroX (p : Point) : Point :=
  { p with x := 0 }
```

この更新記法は既存の値を書き換えるものではない。古い値といくつかのフィールドを共有する新しい値を作るのである。
次の点{anchorName fourAndThree}`fourAndThree`を考える。

```anchor fourAndThree
def fourAndThree : Point :=
  { x := 4.3, y := 3.4 }
```

これを評価し、次に{anchorName zeroX}`zeroX`で更新したものを評価し、もう一度これを評価すると、元の値が得られる。

```anchorTerm fourAndThreeEval
#eval fourAndThree
```


```anchorInfo fourAndThreeEval
{ x := 4.300000, y := 3.400000 }
```


```anchorTerm zeroXFourAndThreeEval
#eval zeroX fourAndThree
```


```anchorInfo zeroXFourAndThreeEval
{ x := 0.000000, y := 3.400000 }
```


```anchorTerm fourAndThreeEval
#eval fourAndThree
```


```anchorInfo fourAndThreeEval
{ x := 4.300000, y := 3.400000 }
```


構造体の更新が元の構造体を書き換えないという事実には、新しい値を古い値から計算する場合の推論が楽になるという利点がある。
古い構造体への参照は、作られたどの新しい値においても、同じフィールドの値を指し続ける。




# 舞台裏
%%%
tag := "behind-the-scenes"
%%%

すべての構造体には*コンストラクタ*がある。
ここで「コンストラクタ」という語は混乱のもとになりうる。
JavaやPythonなどの言語のコンストラクタと違い、Leanのコンストラクタは、データ型の初期化時に走る任意のコードではない。
コンストラクタは、新しく割り当てるデータ構造に格納するデータをまとめるだけのものである。
データを前処理したり、不正な引数を拒否したりする独自のコンストラクタを用意することはできない。
この語は、二つの文脈で似てはいるが異なる意味を持つのである。


既定では、{lit}`S`という名前の構造体のコンストラクタは{lit}`S.mk`という名前になる。
ここで{lit}`S`は名前空間の修飾子であり、{lit}`mk`がコンストラクタ自身の名前である。
淡括弧による初期化の記法を使わず、コンストラクタを直接適用することもできる。

```anchorTerm checkPointMk
#check Point.mk 1.5 2.8
```

ただし、これは一般に良いLeanのスタイルとは見なされていない。Lean自身も、標準の構造体初期化の記法でフィードバックを返す。

```anchorInfo checkPointMk
{ x := 1.5, y := 2.8 } : Point
```


コンストラクタは関数の型を持つので、関数が期待される場所ならどこでも使える。
たとえば{anchorName Pointmk}`Point.mk`は、二つの{anchorName Point}`Float`（それぞれ{anchorName Point}`x`と{anchorName Point}`y`）を受け取り、新しい{anchorName Point}`Point`を返す関数である。

```anchorTerm Pointmk
#check (Point.mk)
```

```anchorInfo Pointmk
Point.mk : Float → Float → Point
```

構造体のコンストラクタの名前を変えるには、先頭にコロンを二つ書く。
たとえば{anchorName Pointmk}`Point.mk`の代わりに{anchorName PointCtorNameName}`Point.point`を使うには、次のように書く。

```anchor PointCtorName
structure Point where
  point ::
  x : Float
  y : Float
```

コンストラクタに加えて、構造体のフィールドごとにアクセサ関数が定義される。
アクセサは、構造体の名前空間の中でフィールドと同じ名前を持つ。
{anchorName Point}`Point`では、アクセサ関数{anchorName Pointx}`Point.x`と{anchorName Pointy}`Point.y`が生成される。

```anchorTerm Pointx
#check (Point.x)
```

```anchorInfo Pointx
Point.x : Point → Float
```

```anchorTerm Pointy
#check (Point.y)
```

```anchorInfo Pointy
Point.y : Point → Float
```


実際、淡括弧による構造体の構築が舞台裏ではコンストラクタの呼び出しに変換されるのと同じように、先ほどの{anchorName addPoints}`addPoints`の定義にある{anchorName addPoints}`x`という記法は、{anchorName addPoints}`x`アクセサの呼び出しに変換される。
つまり、{anchorTerm originx}`#eval origin.x`と{anchorTerm originx1}`#eval Point.x origin`はどちらも次の値を返す。

```anchorInfo originx1
0.000000
```


アクセサのドット記法は、構造体のフィールド以外にも使える。
任意の個数の引数を取る関数にも使える。
より一般に、アクセサ記法は{lit}`TARGET.f ARG1 ARG2 ...`という形をしている。
{lit}`TARGET`の型が{lit}`T`なら、{lit}`T.f`という名前の関数が呼ばれる。
{lit}`TARGET`は、型{lit}`T`を持つ最も左の引数になる。多くの場合は最初の引数だが、常にそうとは限らない。{lit}`ARG1 ARG2 ...`は、残りの引数として順に渡される。
たとえば{anchorName stringAppend}`String.append`は、文字列からアクセサ記法で呼び出せる。{anchorName Inline}`String`が{anchorName stringAppendDot}`append`フィールドを持つ構造体であるわけではないのに、である。

```anchorTerm stringAppendDot
#eval "one string".append " and another"
```

```anchorInfo stringAppendDot
"one string and another"
```

この例では、{lit}`TARGET`が{anchorTerm stringAppendDot}`"one string"`、{lit}`ARG1`が{anchorTerm stringAppendDot}`" and another"`にあたる。

関数{anchorName modifyBoth}`Point.modifyBoth`（{lit}`Point`名前空間で定義された{anchorName modifyBothTest}`modifyBoth`）は、{anchorName Point}`Point`の両方のフィールドに関数を適用する。

```anchor modifyBoth
def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }
```

{anchorName Point}`Point`の引数が関数の引数より後ろにあっても、これもドット記法で使える。

```anchorTerm modifyBothTest
#eval fourAndThree.modifyBoth Float.floor
```

```anchorInfo modifyBothTest
{ x := 4.000000, y := 3.000000 }
```

この場合、{lit}`TARGET`が{anchorName fourAndThree}`fourAndThree`、{lit}`ARG1`が{anchorName modifyBothTest}`Float.floor`である。
アクセサ記法の対象は、型が一致する最初の引数として使われるのであって、必ずしも最初の引数とは限らないためである。

# 練習問題
%%%
tag := "structure-exercises"
%%%

 * 直方体の高さ、幅、奥行きをそれぞれ{anchorName RectangularPrism}`Float`として持つ、{anchorName RectangularPrism}`RectangularPrism`という名前の構造体を定義せよ。
 * 直方体の体積を計算する{anchorTerm RectangularPrism}`volume : RectangularPrism → Float`という名前の関数を定義せよ。
 * 線分を両端の点で表す{anchorName RectangularPrism}`Segment`という名前の構造体を定義し、線分の長さを計算する関数{lit}`length : Segment → Float`を定義せよ。{anchorName RectangularPrism}`Segment`のフィールドは二つ以下とする。
 * {anchorName RectangularPrism}`RectangularPrism`の宣言によって導入される名前はどれか。
 * 次の{anchorName Hamster}`Hamster`と{anchorName Book}`Book`の宣言によって導入される名前はどれか。それぞれの型は何か。

    ```anchor Hamster
    structure Hamster where
      name : String
      fluffy : Bool
    ```

    ```anchor Book
    structure Book where
      makeBook ::
      title : String
      author : String
      price : Float
    ```
