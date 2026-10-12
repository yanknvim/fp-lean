module
public import VersoManual
import FPLean.Examples

import FPLean.DependentTypes.IndexedFamilies
import FPLean.DependentTypes.UniversePattern
import FPLean.DependentTypes.TypedQueries
import FPLean.DependentTypes.IndicesParametersUniverses
import FPLean.DependentTypes.Pitfalls
import FPLean.DependentTypes.Summary

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.DependentTypes"

#doc (Manual) "Programming with Dependent Types" =>
%%%
tag := "dependent-types"
%%%

ほとんどの静的に型付けされたプログラミング言語では、型の世界とプログラムの世界の間に隙間のない壁がある。
型とプログラムは文法が異なり、使われる時期も異なる。
型は通常コンパイル時に、プログラムが一定の不変条件を守っているかを調べるのに使う。
プログラムは実行時に、実際に計算を行うのに使う。
両者が関わるときは通常、「instance-of」の検査のような型の判定や、型検査器にそれまで得られなかった情報を与えて実行時に検証させるキャスト演算子の形を取る。
言い換えれば、その関わりとは、型がプログラムの世界に持ち込まれ、そこで限られた実行時の意味を得ることである。

Leanはこの厳密な分離を課さない。
Leanでは、プログラムが型を計算してもよく、型がプログラムを含んでもよい。
プログラムを型に置くことで、その計算の力をコンパイル時にすべて使えるようになり、関数が型を返せることで、型がプログラミングの過程の第一級の参加者になる。

*依存型*とは、型でない式を含む型である。
依存型のよくある源は、関数の名前付きの引数である。
たとえば{anchorName natOrStringThree}`natOrStringThree`関数は、渡された{anchorName natOrStringThree}`Bool`に応じて自然数か文字列のどちらかを返す。

```anchor natOrStringThree
def natOrStringThree (b : Bool) : if b then Nat else String :=
  match b with
  | true => (3 : Nat)
  | false => "three"
```

依存型のさらなる例には次のものがある。
 * {ref "polymorphism"}[多相についての最初の節]には{anchorName posOrNegThree (module:= Examples.Intro)}`posOrNegThree`があり、関数の戻り値の型が引数の値に依存する。
 * {ref "literal-numbers"}[{anchorName OfNat (module := Examples.Classes)}`OfNat`型クラス]は、使われる具体的な自然数のリテラルに依存する。
 * 検査器の例で使った{ref "validated-input"}[{anchorName CheckedInput (module := Examples.FunctorApplicativeMonad)}`CheckedInput`構造体]は、検査が行われた年に依存する。
 * {ref "subtypes"}[部分型]は、特定の値を参照する命題を含む。
 * {ref "props-proofs-indexing"}[配列の参照記法]の妥当性を決めるものを含め、興味深い命題はほぼすべて、値を含む型であり、したがって依存型である。

依存型は型システムの力を大幅に増やす。
引数の値で分岐する戻り値の型の柔軟さにより、他の型システムでは型を与えるのが難しいプログラムを書けるようになる。
同時に、依存型により、型シグネチャで関数から返してよい値を制限でき、強い不変条件をコンパイル時に強制できる。

しかし、依存型を使ったプログラミングはかなり複雑になりうるし、関数型プログラミングに加えて一そろいの技能が要る。
表現力のある仕様は満たすのが複雑なことがあり、自分で袋小路に陥ってプログラムを完成できなくなる危険も現実にある。
一方、この過程が新たな理解につながることもあり、その理解は満たせる洗練された型として表せる。
この章は依存型を使ったプログラミングの表面をなぞるだけだが、これは一冊の本に値する深い話題である。

{include 1 FPLean.DependentTypes.IndexedFamilies}

{include 1 FPLean.DependentTypes.UniversePattern}

{include 1 FPLean.DependentTypes.TypedQueries}

{include 1 FPLean.DependentTypes.IndicesParametersUniverses}

{include 1 FPLean.DependentTypes.Pitfalls}

{include 1 FPLean.DependentTypes.Summary}
