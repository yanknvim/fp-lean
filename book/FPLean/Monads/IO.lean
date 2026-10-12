module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads.IO"

#doc (Manual) "The IO Monad" =>
%%%
tag := "io-monad"
%%%

モナドとしての{anchorName names}`IO`は二つの観点から理解できる。それらは{ref "running-a-program"}[プログラムの実行]の節で述べた。
どちらの観点も、{anchorName names}`IO`の{anchorName names}`pure`と{anchorName names}`bind`の意味を理解する助けになる。

一つ目の観点では、{anchorName names}`IO`の動作はLeanの実行時システムへの指示である。
たとえば、「このファイル記述子から文字列を読み、その文字列を持って純粋なLeanのコードを呼び直せ」という指示になりうる。
この観点は*外側*からのもので、オペレーティングシステムからプログラムを見る。
この場合、{anchorName names}`pure`は実行時システムに何の副作用も求めない{anchorName names}`IO`の動作であり、{anchorName names}`bind`は、まず副作用を持ちうる操作を一つ実行し、その結果の値を持ってプログラムの残りを呼び出すよう実行時システムに指示する。

二つ目の観点では、{anchorName names}`IO`の動作は世界全体を変換する。
{anchorName names}`IO`の動作は実際には純粋である。唯一の世界を引数として受け取り、変化した世界を返すためである。
この観点は*内側*からのもので、Leanの内部で{anchorName names}`IO`がどう表されるかに一致する。
世界はLeanではトークンとして表され、{anchorName names}`IO`モナドは、各トークンがちょうど一度だけ使われるように組み立てられている。

これがどう働くかを見るには、定義を一つずつはがしていくとよい。
The {kw}`#print`コマンドはLeanのデータ型と定義の中身を明らかにする。
たとえば、
```anchor printNat
#print Nat
```
次の結果になる。
```anchorInfo printNat
inductive Nat : Type
number of parameters: 0
constructors:
Nat.zero : Nat
Nat.succ : Nat → Nat
```
また、
```anchor printStringToLower
#print String.toLower
```
次の結果になる。
```anchorInfo printStringToLower
def String.toLower : String → String :=
fun s => String.map Char.toLower s
```

{kw}`#print`の出力には、この本でまだ紹介していないLeanの機能が含まれることがある。
たとえば、
```anchor printListHeadHuh
#print List.head?
```
次の出力になる。
```anchorInfo printListHeadHuh
def List.head?.{u} : {α : Type u} → List α → Option α :=
fun {α} x =>
  match x with
  | [] => none
  | a :: tail => some a
```
定義の名前の後に{lit}`.{u}`が付き、型が単なる{anchorTerm names}`Type`ではなく{anchorTerm names}`Type u`と注記されている。
今は気にしなくてよい。

{anchorName names}`IO`の定義を表示すると、より単純な構造で定義されていることが分かる。
```anchor printIO
#print IO
```
```anchorInfo printIO
@[reducible] def IO : Type → Type :=
EIO IO.Error
```
{anchorName printIOError}`IO.Error`は、{anchorName names}`IO`の動作が投げうるすべてのエラーを表す。
```anchor printIOError
#print IO.Error
```
```anchorInfo printIOError
inductive IO.Error : Type
number of parameters: 0
constructors:
IO.Error.alreadyExists : Option String → UInt32 → String → IO.Error
IO.Error.otherError : UInt32 → String → IO.Error
IO.Error.resourceBusy : UInt32 → String → IO.Error
IO.Error.resourceVanished : UInt32 → String → IO.Error
IO.Error.unsupportedOperation : UInt32 → String → IO.Error
IO.Error.hardwareFault : UInt32 → String → IO.Error
IO.Error.unsatisfiedConstraints : UInt32 → String → IO.Error
IO.Error.illegalOperation : UInt32 → String → IO.Error
IO.Error.protocolError : UInt32 → String → IO.Error
IO.Error.timeExpired : UInt32 → String → IO.Error
IO.Error.interrupted : String → UInt32 → String → IO.Error
IO.Error.noFileOrDirectory : String → UInt32 → String → IO.Error
IO.Error.invalidArgument : Option String → UInt32 → String → IO.Error
IO.Error.permissionDenied : Option String → UInt32 → String → IO.Error
IO.Error.resourceExhausted : Option String → UInt32 → String → IO.Error
IO.Error.inappropriateType : Option String → UInt32 → String → IO.Error
IO.Error.noSuchThing : Option String → UInt32 → String → IO.Error
IO.Error.unexpectedEof : IO.Error
IO.Error.userError : String → IO.Error
```
{anchorTerm names}`EIO ε α`は、型{anchorName names}`ε`のエラーで終わるか、型{anchorName names}`α`の値で成功する{anchorName names}`IO`の動作を表す。
つまり、{anchorTerm names}`Except ε`モナドと同じく、{anchorName names}`IO`モナドにはエラー処理と例外を定義する能力がある。

もう一段はがすと、{anchorName names}`EIO`自体がより単純な構造で定義されている。
```anchor printEIO
#print EIO
```
```anchorInfo printEIO
def EIO : Type → Type → Type :=
fun ε α => EST ε IO.RealWorld α
```
{anchorName printEStateM}`EST`モナドはエラーと状態の両方を含む。{anchorName names}`Except`と{anchorName State (module := Examples.Monads)}`State`を組み合わせたものに似ている。
これは別の型{anchorName printEStateMResult}`EST.Out`を使って定義されている。
```anchor printEStateM
#print EST
```
```anchorInfo printEStateM
def EST : Type → Type → Type → Type :=
fun ε σ α => Void σ → EST.Out ε σ α
```
言い換えれば、型{anchorTerm EStateMNames}`EST ε σ α`のプログラムは、型{anchorName EStateMNames}`σ`の初期状態を受け取り、{anchorTerm EStateMNames}`EST.Out ε σ α`を返す関数である。
状態は{anchorName VoidSigma}`Void`型で包まれている。これは内部的な原始型で、コンパイルされたコードから値を消し去る。{anchorTerm VoidSigma}`Void σ`は{anchorName save (module:=Examples.Monads)}`Unit`と同じ表現を持つ。

{anchorName EStateMNames}`EST.Out`は{anchorName names}`Except`の定義とよく似ており、成功した終了を示すコンストラクタとエラーを示すコンストラクタがある。
```anchor printEStateMResult
#print EST.Out
```
```anchorInfo printEStateMResult
inductive EST.Out : Type → Type → Type → Type
number of parameters: 3
constructors:
EST.Out.ok : {ε σ α : Type} → α → Void σ → EST.Out ε σ α
EST.Out.error : {ε σ α : Type} → ε → Void σ → EST.Out ε σ α
```
{anchorTerm Except (module:=Examples.Monads)}`Except ε α`と同じく、{anchorName names (show := ok)}`EST.Out.ok`コンストラクタは型{anchorName Except (module:=Examples.Monads)}`α`の結果を含み、{anchorName names (show := error)}`EST.Out.error`コンストラクタは型{anchorName Except (module:=Examples.Monads)}`ε`の例外を含む。
{anchorName names}`Except`と違い、どちらのコンストラクタにも計算の最終状態を含む追加のフィールドがある。

{anchorTerm names}`EST ε σ`の{anchorName names}`Monad`インスタンスには{anchorName names}`pure`と{anchorName names}`bind`が要る。
{anchorName State (module:=Examples.Monads)}`State`と同じく、{anchorName names}`EST`の{anchorName names}`pure`の実装は初期状態を受け取ってそのまま返し、{anchorName names}`Except`と同じく、引数を{anchorName names (show := ok)}`EST.Out.ok`コンストラクタに入れて返す。
```anchor printEStateMpure
#print EST.pure
```
```anchorInfo printEStateMpure
protected def EST.pure : {α ε σ : Type} → α → EST ε σ α :=
fun {α ε σ} a s => EST.Out.ok a s
```
{kw}`protected`は、{anchorName names}`EST`名前空間を開いていても完全な名前{anchorName printEStateMpure}`EST.pure`が必要であることを意味する。

同様に、{anchorName names}`EST`の{anchorName names}`bind`は初期状態を引数に取る。
この初期状態を一つ目の動作に渡す。
{anchorName names}`Except`の{anchorName names}`bind`と同じく、次に結果がエラーかどうかを調べる。
エラーなら、そのエラーをそのまま返し、{anchorName names}`bind`の二つ目の引数は使われない。
結果が成功なら、二つ目の引数を返された値と結果の状態の両方に適用する。
```anchor printEStateMbind
#print EST.bind
```
```anchorInfo printEStateMbind
protected def EST.bind : {ε σ α β : Type} → EST ε σ α → (α → EST ε σ β) → EST ε σ β :=
fun {ε σ α β} x f s =>
  match x s with
  | EST.Out.ok a s => f a s
  | EST.Out.error e s => EST.Out.error e s
```

これらをまとめると、{anchorName names}`IO`は状態とエラーを同時に扱うモナドである。
扱えるエラーの集合は{anchorName printIOError}`IO.Error`データ型で与えられ、プログラムで起こりうる多くの問題を記述するコンストラクタを持つ。
状態は実世界を表す型で、{anchorTerm RealWorld}`IO.RealWorld`という。
{anchorName names}`IO`の基本的な動作はそれぞれこの実世界を受け取り、別の世界を、エラーか結果と組にして返す。
{anchorName names}`IO`では、{anchorName names}`pure`は世界を変えずに返し、{anchorName names}`bind`は変更された世界をある動作から次の動作へ渡す。

宇宙全体はコンピュータのメモリに収まらないので、受け渡される世界は単なる表現である。
世界のトークンが再利用されない限り、その表現は安全である。
{anchorTerm RealWorld}`IO.RealWorld`型はごく単純な原始型で、表現をまったく必要としない。{anchorName VoidSigma}`Void`の内側でしか使われないためである。
