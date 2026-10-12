module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.FunctorApplicativeMonad.ActualDefs"

#doc (Manual) "Summary" =>
%%%
tag := "structure-applicative-monad-summary"
%%%

# 型クラスと構造体
%%%
tag := none
%%%

裏では、型クラスは構造体で表される。
クラスを定義すると構造体が定義され、加えてインスタンスの空の表が作られる。
インスタンスを定義すると、その構造体を型として持つ値か、その構造体を返せる関数が作られ、加えて表に項目が加えられる。
インスタンス探索は、インスタンスの表を参照してインスタンスを組み立てることから成る。
構造体もクラスも、フィールドの既定の値（メソッドの既定の実装）を用意できる。

# 構造体と継承
%%%
tag := none
%%%

構造体は他の構造体を継承できる。
裏では、別の構造体を継承する構造体は、元の構造体の値をフィールドとして持つ。
言い換えれば、継承は合成で実装されている。
多重継承を使うときは、菱形問題を避けるために追加の親構造体の固有のフィールドだけが使われ、通常なら親の値を取り出すはずの関数は、代わりに親を組み立てるように整えられる。
レコードのドット記法は構造体の継承を考慮する。

型クラスは、いくつかの自動化を加えただけの構造体なので、これらの機能はすべて型クラスでも使える。
既定のメソッドと合わせれば、細かいインターフェースの階層を作りつつ、利用者に大きな負担を課さないようにできる。大きなクラスが継承する小さなクラスを自動で実装できるためである。

# アプリカティブファンクタ
%%%
tag := none
%%%

アプリカティブファンクタは、操作が二つ増えたファンクタである。
 * {anchorName Monad}`Monad`と同じ演算子である{anchorName Applicative}`pure`
 * ファンクタの文脈で関数を適用できるようにする{anchorName Seq}`seq`。

モナドは制御の流れを持つ任意のプログラムを表せるが、アプリカティブファンクタは関数の引数を左から右へ実行することしかできない。
より弱いので、そのインターフェースに対して書かれたプログラムに与える制御は少なく、その一方でメソッドの実装者にはより大きな自由度がある。
役に立つ型の中には、{anchorName Applicative}`Applicative`は実装できるが{anchorName Monad}`Monad`は実装できないものがある。

実際、{anchorName HonestFunctor}`Functor`、{anchorName Applicative}`Applicative`、{anchorName Monad}`Monad`という型クラスは力の階層をなしている。
階層を上へ、{anchorName HonestFunctor}`Functor`から{anchorName Monad}`Monad`へ向かうほど、より強力なプログラムを書けるが、より強力なクラスを実装する型は少なくなる。
多相的なプログラムはできるだけ弱い抽象を使うように書き、データ型にはできるだけ強力なインスタンスを与えるとよい。
これでコードの再利用が最大になる。
より強力な型クラスはより弱いものを継承しているので、{anchorName Monad}`Monad`の実装は{anchorName HonestFunctor}`Functor`と{anchorName Applicative}`Applicative`の実装をただで与える。

各クラスには、実装すべきメソッドの集まりと、それらのメソッドについて追加の規則を定める対応する契約がある。
これらのインターフェースに対して書かれたプログラムは、追加の規則が守られることを前提としており、守られなければ不具合を起こしうる。
{anchorName HonestFunctor}`Functor`のメソッドを{anchorName Applicative}`Applicative`のものを使って与える既定の実装、および{anchorName Applicative}`Applicative`のメソッドを{anchorName Monad}`Monad`のものを使って与える既定の実装は、これらの規則を守る。

# 宇宙
%%%
tag := none
%%%

Leanをプログラミング言語としても定理証明器としても使えるようにするには、言語にいくつかの制限が必要である。
これには再帰関数に対する制限が含まれ、すべての再帰関数が停止するか、{kw}`partial`と印を付けられて、値を持たない型を返さないように書かれていることを保証する。
さらに、ある種の論理的な逆理を型として表せてはならない。

ある種の逆理を排除する制限の一つは、すべての型に*宇宙*が割り当てられることである。
宇宙は{anchorTerm extras}`Prop`、{anchorTerm extras}`Type`、{anchorTerm extras}`Type 1`、{anchorTerm extras}`Type 2`などの型である。
これらの型は他の型を記述する。{anchorTerm extras}`0`や{anchorTerm extras}`17`が{anchorName extras}`Nat`で記述されるように、{anchorName extras}`Nat`自体は{anchorTerm extras}`Type`で記述され、{anchorTerm extras}`Type`は{anchorTerm extras}`Type 1`で記述される。
型を引数に取る関数の型は、その引数の宇宙より大きい宇宙でなければならない。

宣言されたデータ型にはそれぞれ宇宙があるので、型をデータのように使うコードを書くとすぐに煩わしくなり、{anchorTerm extras}`Type 1`の引数を取るには多相的な型をいちいちコピーして貼り付ける必要が生じる。
*宇宙多相*と呼ばれる機能により、普通の多相がプログラムに型を引数として取らせるのと同じように、Leanのプログラムとデータ型は宇宙の段階を引数として取れる。
一般に、Leanのライブラリで多相的な操作のライブラリを実装するときは、宇宙多相を使うべきである。
