module
public import VersoManual

import FPLean.Examples

import FPLean.MonadTransformers.ReaderIO
import FPLean.MonadTransformers.Transformers
import FPLean.MonadTransformers.Order
import FPLean.MonadTransformers.Do
import FPLean.MonadTransformers.Conveniences
import FPLean.MonadTransformers.Summary

open Verso.Genre Manual
open Verso Code External

open FPLean


set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads"

#doc (Manual) "Monad Transformers" =>

モナドは、何らかの副作用の集まりを純粋な言語で符号化する手段である。
モナドによって提供する副作用が異なり、状態やエラー処理などがある。
多くのモナドは、非決定的な探索、リーダー、さらには継続のように、ほとんどの言語では使えない役に立つ副作用まで提供する。

典型的なアプリケーションは、モナドを使わずに書かれた試験しやすい関数の核と、必要なアプリケーションの論理を符号化するのにモナドを使う外側の包みから成る。
これらのモナドはよく知られた部品から組み立てられる。
たとえば、
 * 可変状態は、同じ型を持つ関数の引数と戻り値で符号化する。
 * エラー処理は、成功と失敗のコンストラクタを持つ{moduleName}`Except`に似た戻り値の型で符号化する。
 * ログは、戻り値をログと組にすることで符号化する。

しかし、各モナドを手で書くのは面倒で、各種の型クラスの定型の定義が必要になる。
これらの部品はそれぞれ、別のモナドを変更して副作用を一つ加える定義としてくくり出せる。
そのような定義を*モナド変換子*と呼ぶ。
具体的なモナドはモナド変換子の集まりから組み立てられ、これによりコードの再利用がずっと進む。

{include 1 FPLean.MonadTransformers.ReaderIO}

{include 1 FPLean.MonadTransformers.Transformers}

{include 1 FPLean.MonadTransformers.Order}

{include 1 FPLean.MonadTransformers.Do}

{include 1 FPLean.MonadTransformers.Conveniences}

{include 1 FPLean.MonadTransformers.Summary}
