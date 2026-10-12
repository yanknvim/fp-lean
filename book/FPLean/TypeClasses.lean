module
public import VersoManual
import FPLean.Examples

import FPLean.TypeClasses.Pos
import FPLean.TypeClasses.Polymorphism
import FPLean.TypeClasses.OutParams
import FPLean.TypeClasses.Indexing
import FPLean.TypeClasses.Coercions
import FPLean.TypeClasses.Conveniences
import FPLean.TypeClasses.StandardClasses
import FPLean.TypeClasses.Summary

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true

#doc (Manual) "Overloading and Type Classes" =>
%%%
tag := "type-classes"
%%%

多くの言語では、組み込みのデータ型が特別扱いされる。
たとえばCやJavaでは、{lit}`+`で{c}`float`や{c}`int`は足せるが、第三者のライブラリが提供する任意精度の数は足せない。
同様に、数値リテラルは組み込みの型にはそのまま使えるが、利用者が定義した数の型には使えない。
他の言語には演算子の{deftech}*オーバーロード*の仕組みがあり、同じ演算子に新しい型での意味を与えられる。
C++やC#のような言語では、さまざまな組み込み演算子をオーバーロードでき、コンパイラは型検査を使ってどの実装を選ぶかを決める。

数値リテラルや演算子だけでなく、多くの言語では関数やメソッドのオーバーロードもできる。
C++、Java、C#、Kotlinでは、引数の個数や型が異なる複数の実装を同じメソッドに持たせられる。
コンパイラは引数の個数と型から、どのオーバーロードを意図したかを判断する。

関数と演算子のオーバーロードには重要な制限がある。多相関数は、型引数をそのオーバーロードが存在する型に限定できないのである。
たとえば、文字列、バイト配列、ファイルポインタに対してオーバーロードされたメソッドがあっても、そのどれに対しても使える第2のメソッドを書く方法がない。
代わりに、その第2のメソッドを、元のメソッドのオーバーロードがある型ごとにオーバーロードしなければならず、一つの多相的な定義ではなく、多くの定型定義が必要になる。
この制限のもう一つの帰結は、一部の演算子（Javaの等価演算子など）が、妥当とは限らない*あらゆる*引数の組み合わせに対して定義されることである。
プログラマが十分注意しないと、実行時にクラッシュしたり、黙って誤った結果を計算したりするプログラムになりうる。

Leanは、Haskellで先駆けて導入された{deftech}*型クラス*という仕組みでオーバーロードを実装している。演算子、関数、リテラルのオーバーロードを、多相性と相性よく行える。
型クラスは、オーバーロードできる操作の集まりを記述する。
新しい型でこれらの操作をオーバーロードするには、その型に対する各操作の実装を持つ*インスタンス*を作る。
たとえば{anchorName chapterIntro}`Add`という型クラスは加法が定義できる型を記述し、{anchorTerm chapterIntro}`Nat`に対する{anchorTerm chapterIntro}`Add`のインスタンスが{anchorTerm chapterIntro}`Nat`の加法の実装を与える。

*クラス*と*インスタンス*という語は、オブジェクト指向言語に慣れた人には紛らわしいかもしれない。オブジェクト指向言語のクラスとインスタンスとはあまり関係がないためである。
ただし、語源は共通している。日常の言葉で「クラス」は、共通の性質を持つ集まりを指す。
オブジェクト指向プログラミングのクラスも、確かに共通の性質を持つオブジェクトの集まりを記述するが、それに加えて、そのような集まりを記述するための言語の特定の仕組みを指す。
型クラスも、共通の性質（つまり特定の操作の実装）を共有する型を記述する手段だが、オブジェクト指向プログラミングのクラスとは、それ以外に共通点はほとんどない。

Leanの型クラスは、JavaやC#の*インターフェース*にはるかに近い。
型クラスもインターフェースも、ある型または型の集まりに対して実装される、概念上関連した操作の集合を記述する。
同様に、型クラスのインスタンスは、JavaやC#のクラスのインスタンスというより、実装しているインターフェースによって定められるコードに近い。
JavaやC#のインターフェースと違い、型の作者が手を入れられない型クラスに対しても、その型のインスタンスを与えられる。
この点では、Rustのトレイトとよく似ている。

{include 1 FPLean.TypeClasses.Pos}

{include 1 FPLean.TypeClasses.Polymorphism}

{include 1 FPLean.TypeClasses.OutParams}

{include 1 FPLean.TypeClasses.Indexing}

{include 1 FPLean.TypeClasses.StandardClasses}

{include 1 FPLean.TypeClasses.Coercions}

{include 1 FPLean.TypeClasses.Conveniences}

{include 1 FPLean.TypeClasses.Summary}
