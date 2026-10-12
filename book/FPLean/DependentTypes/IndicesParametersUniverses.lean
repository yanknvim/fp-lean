module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.DependentTypes.IndicesParameters"

#doc (Manual) "Indices, Parameters, and Universe Levels" =>
%%%
tag := "indices-parameters-universe-levels"
%%%

帰納型の添字とパラメータの区別は、コンストラクタ間で変わるか変わらないかによって型への引数を記述する手段にとどまらない。
帰納型への引数がパラメータか添字かは、それらの宇宙の段階の関係を決めるときにも問題になる。
特に、帰納型はパラメータと同じ宇宙の段階を持ってよいが、添字より大きな宇宙になければならない。
この制限は、Leanをプログラミング言語としてだけでなく定理証明器としても使えるようにするのに必要である。これがなければLeanの論理は矛盾する。
エラーメッセージを試すのは、これらの規則と、型への引数がパラメータか添字かを決める正確な規則を示すよい方法である。

一般に、帰納型の定義ではパラメータをコロンの前に、添字をコロンの後に置く。
パラメータは関数の引数のように名前を付けるが、添字はその型を記述するだけである。
これは{anchorName Vect (module := Examples.DependentTypes)}`Vect`の定義に見られる。

```anchor Vect (module := Examples.DependentTypes)
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
```
この定義で{anchorName Vect (module:=Examples.DependentTypes)}`α`はパラメータであり、{anchorName Vect (module:=Examples.DependentTypes)}`Nat`は添字である。
パラメータは定義全体で参照してよい（たとえば{anchorName consNotLengthN (module:=Examples.DependentTypes)}`Vect.cons`は最初の引数の型に{anchorName Vect (module:=Examples.DependentTypes)}`α`を使う）が、常に一貫して使わねばならない。
添字は変わることが想定されているので、データ型の定義の先頭で引数として与えるのではなく、各コンストラクタで個々の値が割り当てられる。


パラメータを持つごく単純なデータ型が{anchorName WithParameter}`WithParameter`である。

```anchor WithParameter
inductive WithParameter (α : Type u) : Type u where
  | test : α → WithParameter α
```
宇宙の段階{anchorTerm WithParameter}`u`をパラメータにも帰納型自体にも使える。これは、パラメータがデータ型の宇宙の段階を上げないことを示している。
同様に、パラメータが複数あるとき、帰納型はより大きなほうの宇宙の段階を受け取る。

```anchor WithTwoParameters
inductive WithTwoParameters (α : Type u) (β : Type v) : Type (max u v) where
  | test : α → β → WithTwoParameters α β
```
パラメータはデータ型の宇宙の段階を上げないので、扱いやすいことがある。
Leanは、添字のように（コロンの後に）記述されていてもパラメータのように使われている引数を見つけ出し、パラメータにしようとする。
次の二つの帰納的データ型はどちらもパラメータをコロンの後に書いている。

```anchor WithParameterAfterColon
inductive WithParameterAfterColon : Type u → Type u where
  | test : α → WithParameterAfterColon α
```

```anchor WithParameterAfterColon2
inductive WithParameterAfterColon2 : Type u → Type u where
  | test1 : α → WithParameterAfterColon2 α
  | test2 : WithParameterAfterColon2 α
```

パラメータがデータ型の最初の宣言で名前を付けられていないときは、一貫して使う限り、コンストラクタごとに違う名前を使ってもよい。
次の宣言は受け付けられる。

```anchor WithParameterAfterColonDifferentNames
inductive WithParameterAfterColonDifferentNames : Type u → Type u where
  | test1 : α → WithParameterAfterColonDifferentNames α
  | test2 : β → WithParameterAfterColonDifferentNames β
```
しかし、この柔軟さはパラメータの名前を明示的に宣言したデータ型には及ばない。
```anchor WithParameterBeforeColonDifferentNames
inductive WithParameterBeforeColonDifferentNames (α : Type u) : Type u where
  | test1 : α → WithParameterBeforeColonDifferentNames α
  | test2 : β → WithParameterBeforeColonDifferentNames β
```
```anchorError WithParameterBeforeColonDifferentNames
Mismatched inductive type parameter in
  WithParameterBeforeColonDifferentNames β
The provided argument
  β
is not definitionally equal to the expected parameter
  α

Note: The value of parameter `α` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
```
同様に、添字に名前を付けようとするとエラーになる。
```anchor WithNamedIndex
inductive WithNamedIndex (α : Type u) : Type (u + 1) where
  | test1 : WithNamedIndex α
  | test2 : WithNamedIndex α → WithNamedIndex α → WithNamedIndex (α × α)
```
```anchorError WithNamedIndex
Mismatched inductive type parameter in
  WithNamedIndex (α × α)
The provided argument
  α × α
is not definitionally equal to the expected parameter
  α

Note: The value of parameter `α` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
```

適切な宇宙の段階を使い、添字をコロンの後に置けば、受け付けられる宣言になる。

```anchor WithIndex
inductive WithIndex : Type u → Type (u + 1) where
  | test1 : WithIndex α
  | test2 : WithIndex α → WithIndex α → WithIndex (α × α)
```


帰納型の宣言でコロンの後の引数がすべてのコンストラクタで一貫して使われているとき、Leanがそれをパラメータだと判断できることもあるが、それでもパラメータはすべて添字より前に来る必要がある。
パラメータを添字の後に置こうとすると、その引数自体が添字と見なされ、データ型の宇宙の段階を上げる必要が生じる。
```anchor ParamAfterIndex
inductive ParamAfterIndex : Nat → Type u → Type u where
  | test1 : ParamAfterIndex 0 γ
  | test2 : ParamAfterIndex n γ → ParamAfterIndex k γ → ParamAfterIndex (n + k) γ
```
```anchorError ParamAfterIndex
Invalid universe level in constructor `ParamAfterIndex.test1`: Parameter `γ` has type
  Type u
at universe level
  u + 2
which is not less than or equal to the inductive type's resulting universe level
  u + 1
```

パラメータは型である必要はない。
この例は、{anchorName NatParamFour}`Nat`のような普通のデータ型もパラメータに使えることを示している。
```anchor NatParamFour
inductive NatParam (n : Nat) : Nat → Type u where
  | five : NatParam 4 5
```
```anchorError NatParamFour
Mismatched inductive type parameter in
  NatParam 4 5
The provided argument
  4
is not definitionally equal to the expected parameter
  n

Note: The value of parameter `n` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
```
示唆どおりに{anchorName NatParam}`n`を使うと、その宣言は受け付けられる。

```anchor NatParam
inductive NatParam (n : Nat) : Nat → Type u where
  | five : NatParam n 5
```




これらの実験から何が結論できるか。
パラメータと添字の規則は次のとおりである。
 1. パラメータは各コンストラクタの型で同じように使わねばならない。
 2. パラメータはすべて添字より前に来なければならない。
 3. 定義するデータ型の宇宙の段階は、最も大きなパラメータ以上で、最も大きな添字より真に大きくなければならない。
 4. コロンの前に書かれた名前付きの引数は常にパラメータであり、コロンの後の引数は通常は添字である。Leanは、コロンの後の引数がすべてのコンストラクタで一貫して使われ、かつどの添字よりも後に来ないなら、その使い方からそれらをパラメータだと判断することがある。

迷ったときは、Leanの{kw}`#print`コマンドで、データ型の引数のうちいくつがパラメータかを調べられる。
たとえば{anchorTerm printVect}`Vect`については、パラメータの数が1であると指摘する。
```anchor printVect
#print Vect
```
```anchorInfo printVect
inductive Vect.{u} : Type u → Nat → Type u
number of parameters: 1
constructors:
Vect.nil : {α : Type u} → Vect α 0
Vect.cons : {α : Type u} → {n : Nat} → α → Vect α n → Vect α (n + 1)
```

データ型への引数の順序を選ぶときは、どの引数をパラメータにし、どれを添字にすべきかを考える価値がある。
できるだけ多くの引数をパラメータにすると宇宙の段階を抑えられ、複雑なプログラムの型検査が通りやすくなることがある。
それを可能にする一つの方法は、引数の並びでパラメータをすべて添字より前にすることである。

さらに、Leanがコロンの後の引数を使い方からパラメータだと判断できるとしても、パラメータは明示的に名前を付けて書くのがよい。
そうすれば読み手に意図が明確になり、その引数が誤ってコンストラクタ間で一貫しない使われ方をしたときにLeanがエラーを報告する。
