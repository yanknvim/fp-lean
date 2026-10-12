module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.SpecialTypes"

#doc (Manual) "Special Types" =>
%%%
tag := "runtime-special-types"
%%%

メモリ内でのデータの表現を理解することは非常に重要である。
通常、その表現はデータ型の定義から理解できる。
各コンストラクタはメモリ内のオブジェクトに対応し、そのオブジェクトはタグと参照カウントを含むヘッダを持つ。
コンストラクタの引数はそれぞれ、別のオブジェクトへのポインタで表される。
言い換えれば、{anchorName all}`List`は本当に連結リストであり、{kw}`structure`からフィールドを取り出すのは本当にポインタをたどるだけである。

しかし、この規則には重要な例外がいくつかある。
いくつかの型はコンパイラによって特別に扱われる。
たとえば、型{anchorName all}`UInt32`は{anchorTerm all}`Fin (2 ^ 32)`として定義されているが、実行時には機械語に基づく実際のネイティブな実装で置き換えられる。
同様に、{anchorName all}`Nat`の定義は{anchorTerm all}`List Unit`に似た実装を示唆しているが、実際の実行時の表現は、十分小さい数には即値の機械語を使い、より大きな数には効率のよい任意精度算術のライブラリを使う。
Leanのコンパイラは、パターンマッチングを使う定義をこの表現に適した操作へ変換し、加算や減算のような操作の呼び出しは、その下の算術ライブラリの高速な操作に対応付けられる。
何しろ、加算に加数の大きさに線形な時間がかかってはならない。

一部の型が特別な表現を持つということは、それらを扱うときに注意が要るということでもある。
これらの型のほとんどは、コンパイラが特別に扱う{kw}`structure`から成る。
これらの構造体では、コンストラクタやフィールドアクセサを直接使うと、効率のよい表現と、証明で使うために設計された表現の間の費用のかかる変換が引き起こされうる。

たとえば、配列は連結リストを包む構造体として定義されている。
コンパイル済みのコードでは、それらは効率のよい動的配列として表され、コンストラクタ{moduleName}`Array.mk`をリストに適用するとそのリストがそのような効率のよい配列に変換され、線形の時間がかかる。
フィールドアクセサ{anchorName sequences}`toList`はその配列を連結リストに戻し、これも線形の時間がかかる。
この{anchorName sequences}`Array`の定義は、配列についての証明を容易にするためだけに存在しており、動かすつもりのコードではこれらの変換を避けるべきである。
同様に、{anchorName all}`String`は、バイトの配列と、そのバイトが正しいUTF-8であるという証明を含む構造体として定義されているが、実行時の表現にはさらに、文字列の文字数をキャッシュするフィールドが含まれる。
コンストラクタをバイト配列に適用できるのはそのバイト配列が妥当なときだけなので、そのバイトが実際にUTF-8の並びであるかを調べる必要はないが、文字数は線形の時間で計算される。
アクセサ{anchorName StringDetail}`toByteArray`は新しいバイト配列のオブジェクトを確保してその下のバイトを複製し、線形の時間と空間を要する。
文字列に対する基本操作の多くは、コンパイラによって効率のよい版に置き換えられ、可能なときは新しいものを確保する代わりにその文字列の実行時の表現を変更する。


型自体も命題の証明も、コンパイル済みのコードから完全に消し去られる。
言い換えれば、それらは空間を取らず、証明の一部として行われたかもしれない計算も同様に消し去られる。
つまり、証明は、配列に対する帰納的に定義されたリストとしての便利なインターフェースを利用でき、それについて帰納法を使って証明することもできるが、プログラムの実行中に遅い変換の段階を課すことはない。
これらの組み込みの型では、データの便利な論理的な表現が、プログラムが遅くなければならないことを意味するわけではない。

構造体型が、型でも証明でもないフィールドを一つしか持たないなら、そのコンストラクタ自体は実行時に消え、その唯一の引数で置き換えられる。
言い換えれば、部分型はその下の型とまったく同じように表され、余分な間接の層はない。
同様に、{anchorName all}`Fin`はメモリ内では単なる{anchorName all}`Nat`であり、性能の負担を払わずに{anchorName all}`Nat`や{anchorName all}`String`の異なる用途を追跡するために、フィールドが一つの構造体を作れる。
コンストラクタが、型でも証明でもない引数を持たないなら、そのコンストラクタも消え、ポインタが使われるはずの場所で定数値に置き換えられる。
つまり、{anchorName all}`true`、{anchorName all}`false`、{anchorName all}`none`は、ヒープに確保されたオブジェクトへのポインタではなく、定数値である。


次の型は特別な表現を持つ。

:::table +header
*
  * 型
  * 論理的な表現
  * 実行時の表現

*
  * {anchorName all}`Nat`
  * 一進法で、各{anchorTerm all}`Nat.succ`からポインタが一つ
  * 効率のよい任意精度整数

*
  * {anchorName all}`Int`
  * 正か負の値のコンストラクタを持ち、それぞれが{anchorName all}`Nat`を含む直和型
  * 効率のよい任意精度整数

*
  * {anchorTerm all}`BitVec w`
  * 適切な上限$`2^w`を持つ{anchorName all}`Fin`
  * 効率のよい任意精度整数

*
  * {anchorName all}`UInt8`, {anchorName all}`UInt16`, {anchorName all}`UInt32`, {anchorName all}`UInt64`, {anchorName all}`USize`
  * 正しい幅のビットベクトル
  * 固定精度の機械整数

*
  * {anchorName all}`Int8`, {anchorName all}`Int16`, {anchorName all}`Int32`, {anchorName all}`Int64`, {anchorName all}`ISize`
  * 同じ幅の符号なし整数を包んだもの
  * 固定精度の機械整数

*
  * {anchorName all}`Char`
  * {anchorName all}`UInt32`と、それが妥当な符号位置であるという証明の組
  * 普通の文字

*
  * {anchorName all}`String`
  * {anchorTerm StringDetail}`toByteArray`というフィールドに{anchorTerm StringDetail}`ByteArray`を含み、その配列が妥当なUTF-8であるという証明を伴う構造体
  * UTF-8で符号化された文字列と文字数

*
  * {anchorTerm sequences}`Array α`
  * {anchorName sequences}`toList`というフィールドに{anchorTerm sequences}`List α`を含む構造体
  * {anchorName sequences}`α`の値へのポインタを詰めた配列

*
  * {anchorTerm all}`Sort u`
  * 型
  * 完全に消し去られる

*
  * 命題の証明
  * その命題が証拠の型として見なされるときに示唆するデータ
  * 完全に消し去られる
:::


# 練習問題
%%%
tag := "runtime-special-types-exercise"
%%%

{ref "positive-numbers"}[{anchorName Pos (module := Examples.Classes)}`Pos`の定義]は、Leanが{anchorName all}`Nat`を効率のよい型にコンパイルすることを利用していない。
実行時には、それは本質的に連結リストである。
あるいは、{ref "subtypes"}[部分型についての最初の節]で述べたように、Leanの高速な{anchorName all}`Nat`型を内部で使える部分型を定義できる。
実行時には、その証明は消し去られる。
得られる構造体はデータのフィールドを一つしか持たないので、そのフィールドとして表され、つまりこの新しい{anchorName Pos (module := Examples.Classes)}`Pos`の表現は{anchorName all}`Nat`のものと同一である。

定理{anchorTerm all}`∀ {n k : Nat}, n ≠ 0 → k ≠ 0 → n + k ≠ 0`を証明した後、この新しい{anchorName Pos (module := Examples.Classes)}`Pos`の表現について{anchorName all}`ToString`と{anchorName all}`Add`のインスタンスを定義せよ。 次に{anchorName all}`Mul`のインスタンスを定義し、途中で必要な定理を証明せよ。
