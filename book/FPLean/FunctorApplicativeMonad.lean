module
public import VersoManual
import FPLean.Examples
import FPLean.FunctorApplicativeMonad.Inheritance
import FPLean.FunctorApplicativeMonad.Applicative
import FPLean.FunctorApplicativeMonad.ApplicativeContract
import FPLean.FunctorApplicativeMonad.Alternative
import FPLean.FunctorApplicativeMonad.Universes
import FPLean.FunctorApplicativeMonad.Complete
import FPLean.FunctorApplicativeMonad.Summary


open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.FunctorApplicativeMonad"

#doc (Manual) "Functors, Applicative Functors, and Monads" =>

{anchorTerm FunctorPair}`Functor`と{moduleName}`Monad`はどちらも、型引数をまだ待っている型のための操作を記述する。
それらを理解する一つの方法は、{anchorTerm FunctorPair}`Functor`は中に入ったデータを変換できる容器を記述し、{moduleName}`Monad`は副作用を持つプログラムの符号化を記述する、と見ることである。
しかしこの理解は完全ではない。
何しろ{moduleName}`Option`は{moduleName}`Functor`と{moduleName}`Monad`の両方のインスタンスを持ち、省略可能な値*であり*、値を返すのに失敗しうる計算*でも*ある。

データ構造の観点では、{anchorName AlternativeOption}`Option`はnull許容型か、要素を高々一つしか持てないリストに少し似ている。
制御構造の観点では、{anchorName AlternativeOption}`Option`は結果を出さずに途中で終わりうる計算を表す。
ふつう、{anchorName FunctorValidate}`Functor`インスタンスを使うプログラムは{anchorName AlternativeOption}`Option`をデータ構造として使うものと考えるのが最も分かりやすく、{anchorName MonadExtends}`Monad`インスタンスを使うプログラムは{anchorName AlternativeOption}`Option`で早期の失敗を可能にするものと考えるのが最も分かりやすい。しかし、どちらの観点も自在に使えるようになることは、関数型プログラミングに熟達するうえで重要な部分である。

ファンクタとモナドの間にはより深い関係がある。
*すべてのモナドはファンクタである*ことが分かる。
言い換えれば、モナドという抽象はファンクタという抽象より強力である。すべてのファンクタがモナドなわけではないためである。
さらに、*アプリカティブファンクタ*と呼ばれる中間の抽象があり、多くの興味深いプログラムを書けるだけの力を持ちながら、{anchorName MonadExtends}`Monad`インターフェースを使えないライブラリも許す。
{anchorName ApplicativeValidate}`Applicative`型クラスがアプリカティブファンクタのオーバーロード可能な操作を与える。
すべてのモナドはアプリカティブファンクタであり、すべてのアプリカティブファンクタはファンクタであるが、逆は成り立たない。

{include 1 FPLean.FunctorApplicativeMonad.Inheritance}

{include 1 FPLean.FunctorApplicativeMonad.Applicative}

{include 1 FPLean.FunctorApplicativeMonad.ApplicativeContract}

{include 1 FPLean.FunctorApplicativeMonad.Alternative}

{include 1 FPLean.FunctorApplicativeMonad.Universes}

{include 1 FPLean.FunctorApplicativeMonad.Complete}

{include 1 FPLean.FunctorApplicativeMonad.Summary}
