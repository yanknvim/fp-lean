module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.DependentTypes.Pitfalls"

#doc (Manual) "Pitfalls of Programming with Dependent Types" =>
%%%
tag := "dependent-type-pitfalls"
%%%

依存型の柔軟さにより、より役に立つプログラムが型検査器に受け入れられる。型の言語が、表現力の低い型システムでは記述できない変種を記述できるだけの表現力を持つためである。
同時に、依存型が非常に細かい仕様を表現できることにより、より多くの不具合のあるプログラムが型検査器に拒否される。
この力には代償がある。

{anchorName Row (module:=Examples.DependentTypes.DB)}`Row`のような型を返す関数の中身と、それが生み出す型との密接な結び付きは、より大きな難点の一例である。関数を型に使うと、関数のインターフェースと実装の区別が崩れ始めるのである。
通常は、関数の型シグネチャや入力と出力の振る舞いを変えない限り、どのような書き換えも有効である。
より効率のよい算法やデータ構造を使うように関数を書き換えたり、不具合を直したり、コードの明快さを改善したりしても、利用側のコードを壊さない。
しかし、その関数を型に使うと、関数の実装の中身が型の一部になり、したがって別のプログラムに対する*インターフェース*の一部になる。

例として、{anchorName plusL}`Nat`の加法の次の二つの実装を考えよう。
{anchorName plusL}`Nat.plusL`は一つ目の引数について再帰的である。

```anchor plusL
def Nat.plusL : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => plusL n k + 1
```
一方、{anchorName plusR}`Nat.plusR`は二つ目の引数について再帰的である。

```anchor plusR
def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => plusR n k + 1
```
どちらの加法の実装も、その下にある数学的な概念に忠実であり、したがって同じ引数を与えれば同じ結果を返す。

しかし、この二つの実装は、型に使うとかなり違うインターフェースを呈する。
例として、二つの{anchorName appendL}`Vect`を連結する関数を考えよう。
この関数は、長さが引数の長さの和である{anchorName appendL}`Vect`を返すべきである。
{anchorName appendL}`Vect`は本質的にはより情報量の多い型を持つ{anchorName moreNames}`List`なので、{anchorName moreNames}`List.append`と同じように、一つ目の引数についてのパターンマッチングと再帰で関数を書くのは理にかなっている。
型シグネチャと、穴埋めを指す最初のパターンマッチから始めると、二つのメッセージが出る。
```anchor appendL1
def appendL : Vect α n → Vect α k → Vect α (n.plusL k)
  | .nil, ys => _
  | .cons x xs, ys => _
```
一つ目のメッセージは{anchorName moreNames}`nil`の場合についてで、穴埋めを長さ{lit}`plusL 0 k`の{anchorName appendL}`Vect`に置き換えるべきことを述べている。
```anchorError appendL1
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
ys : Vect α k
⊢ Vect α (Nat.plusL 0 k)
```
二つ目のメッセージは{anchorName moreNames}`cons`の場合についてで、穴埋めを長さ{lit}`plusL (n✝ + 1) k`の{anchorName appendL}`Vect`に置き換えるべきことを述べている。
```anchorError appendL2
don't know how to synthesize placeholder
context:
α : Type u_1
n k n✝ : Nat
x : α
xs : Vect α n✝
ys : Vect α k
⊢ Vect α ((n✝ + 1).plusL k)
```
{lit}`n`の後の記号は*ダガー*と呼ばれ、Leanが内部で作り出した名前を示すのに使う。
裏では、一つ目の{anchorName appendL1}`Vect`でのパターンマッチングにより、一つ目の{anchorName plusL}`Nat`の値も暗黙に洗練された。{anchorName moreNames}`cons`コンストラクタの添字が{anchorTerm Vect (module:=Examples.DependentTypes)}`n + 1`であり、その{anchorName appendL}`Vect`の残りの長さが{anchorTerm Vect (module:=Examples.DependentTypes)}`n`だからである。
ここで{lit}`n✝`は、引数{anchorName appendL1}`n`より一つ小さい{anchorName moreNames}`Nat`を表す。

# 定義上の等しさ
%%%
tag := "definitional-equality"
%%%

{anchorName appendL3}`plusL`の定義には、パターンの場合{anchorTerm plusL}`0, k => k`がある。
これは一つ目の穴埋めで使う長さに当てはまるので、そのアンダースコアの型{anchorTerm moreNames}`Vect α (Nat.plusL 0 k)`は{anchorTerm moreNames}`Vect α k`とも書ける。
同様に、{anchorName plusL}`plusL`にはパターンの場合{anchorTerm plusL}`n + 1, k => plusL n k + 1`がある。
つまり、二つ目のアンダースコアの型は{lit}`Vect α (plusL n✝ k + 1)`とも等価に書ける。

裏で何が起きているかを明らかにするには、まず{anchorName plusL}`Nat`の引数を明示的に書く。そうすると名前がプログラムに明示的に書かれているので、ダガーのないエラーメッセージにもなる。
```anchor appendL3
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => _
  | n + 1, k, .cons x xs, ys => _
```
```anchorError appendL3
don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α (Nat.plusL 0 k)
```
```anchorError appendL4
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α ((n + 1).plusL k)
```
アンダースコアに単純化した版の型を注記しても型エラーは起きない。つまり、プログラムに書いた型はLeanが自力で見つけた型と等価である。
```anchor appendL5
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => (_ : Vect α (n.plusL k + 1))
```
```anchorError appendL5
don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α k
```
```anchorError appendL6
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α (n.plusL k + 1)
```

一つ目の場合は{anchorTerm appendL5}`Vect α k`を要求し、{anchorName appendL5}`ys`がその型を持つ。
これは、空のリストを他のどのリストに連結してもそのリストが返るのと対応している。
一つ目のアンダースコアの代わりに{anchorName appendL7}`ys`で定義を洗練すると、埋めるべきアンダースコアが一つだけ残ったプログラムになる。
```anchor appendL7
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => ys
  | n + 1, k, .cons x xs, ys => (_ : Vect α (n.plusL k + 1))
```
```anchorError appendL7
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α (n.plusL k + 1)
```

ここで非常に重要なことが起きている。
Leanが{anchorTerm moreNames}`Vect α (Nat.plusL 0 k)`を期待した文脈で、{anchorTerm moreNames}`Vect α k`を受け取ったのである。
しかし{anchorName plusL}`Nat.plusL`は{kw}`abbrev`ではないので、型検査の間に動くはずがないように思える。
何か別のことが起きている。

何が起きているかを理解する鍵は、Leanが型検査の間に{kw}`abbrev`を展開するだけではないということである。
Leanは、二つの型が互いに等価かどうかを調べる間にも計算を行える。ある型の式を、他方の型を期待する文脈で使えるようにするためである。
この性質を*定義上の等しさ*と呼び、これは微妙である。

もちろん、同じように書かれた二つの型は定義上等しいと見なされる。{anchorName moreNames}`Nat`と{anchorName moreNames}`Nat`、あるいは{anchorTerm moreNames}`List String`と{anchorTerm moreNames}`List String`は等しいと見なすべきである。
異なるデータ型から作られた二つの具体的な型は等しくないので、{anchorTerm moreNames}`List Nat`は{anchorName moreNames}`Int`と等しくない。
さらに、内部の名前を付け替えただけの型は等しいので、{anchorTerm moreNames}`(n : Nat) → Vect String n`は{anchorTerm moreNames}`(k : Nat) → Vect String k`と同じである。
型は普通のデータを含みうるので、定義上の等しさはデータがいつ等しいかも記述せねばならない。
同じコンストラクタを使ったものは等しいので、{anchorTerm moreNames}`0`は{anchorTerm moreNames}`0`と、{anchorTerm moreNames}`[5, 3, 1]`は{anchorTerm moreNames}`[5, 3, 1]`と等しい。

しかし、型は関数の矢印やデータ型、コンストラクタだけを含むのではない。
型は*変数*と*関数*も含む。
変数の定義上の等しさは比較的単純である。各変数はそれ自身にしか等しくないので、{anchorTerm moreNames}`(n k : Nat) → Vect Int n`は{anchorTerm moreNames}`(n k : Nat) → Vect Int k`と定義上等しくない。
一方、関数はもっと複雑である。
数学では二つの関数が同じ入力と出力の振る舞いを持てば等しいと見なすが、それを調べる効率のよい算法はなく、定義上の等しさの狙いは、二つの型が差し替え可能かをLeanが調べることにある。
代わりにLeanは、どちらも本体が定義上等しい{kw}`fun`式であるときに、その二つの関数を定義上等しいと見なす。
言い換えれば、二つの関数が定義上等しいと見なされるには、*同じ補助関数*を呼ぶ*同じ算法*を使わねばならない。
これは通常あまり役に立たないので、関数の定義上の等しさは、まったく同じ定義済みの関数が二つの型に現れるときに主に使われる。

型の中で関数が*呼び出されると*、定義上の等しさの検査に関数の呼び出しを簡約することが含まれうる。
型{anchorTerm moreNames}`Vect String (1 + 4)`は型{anchorTerm moreNames}`Vect String (3 + 2)`と定義上等しい。{anchorTerm moreNames}`1 + 4`が{anchorTerm moreNames}`3 + 2`と定義上等しいためである。
その等しさを調べるには、どちらも{anchorTerm moreNames}`5`に簡約し、次にコンストラクタの規則を五度使えばよい。
データに適用された関数の定義上の等しさは、まずそれらがすでに同じかどうかを見て調べられる。何しろ{anchorTerm moreNames}`["a", "b"] ++ ["c"]`が{anchorTerm moreNames}`["a", "b"] ++ ["c"]`と等しいかを調べるのに簡約する必要はない。
そうでなければ、その関数が呼び出されてその値に置き換えられ、次にその値を調べられる。

関数の引数がすべて具体的なデータであるわけではない。
たとえば、型には{anchorName moreNames}`zero`と{anchorName moreNames}`succ`のコンストラクタから作られていない{anchorName moreNames}`Nat`が含まれうる。
型{anchorTerm moreFun}`(n : Nat) → Vect String n`で、変数{anchorName moreFun}`n`は{anchorName moreFun}`Nat`だが、その関数が呼ばれる前に*どの*{anchorName moreFun}`Nat`かを知ることはできない。
実際、その関数はまず{anchorTerm moreNames}`0`で、次に{anchorTerm moreNames}`17`で、さらに{anchorTerm moreNames}`33`で呼ばれるかもしれない。
{anchorName appendL}`appendL`の定義に見られるように、{anchorName moreFun}`Nat`型の変数は{anchorName appendL}`plusL`のような関数に渡されることもある。
実際、型{anchorTerm moreFun}`(n : Nat) → Vect String n`は型{anchorTerm moreNames}`(n : Nat) → Vect String (Nat.plusL 0 n)`と定義上等しい。

{anchorName againFun}`n`と{anchorTerm againFun}`Nat.plusL 0 n`が定義上等しいのは、{anchorName plusL}`plusL`のパターンマッチングが*一つ目*の引数を調べるためである。
これは問題である。{anchorTerm moreFun}`(n : Nat) → Vect String n`は{anchorTerm stuckFun}`(n : Nat) → Vect String (Nat.plusL n 0)`と定義上等しく*ない*。0は加法の左単位元でも右単位元でもあるはずなのに、である。
これは、パターンマッチングが変数に出会うと行き詰まるために起きる。
{anchorName stuckFun}`n`の実際の値が分かるまでは、{anchorTerm stuckFun}`Nat.plusL n 0`のどの場合を選ぶべきかを知る手立てがない。

同じ問題は、問い合わせの例の{anchorName Row (module:=Examples.DependentTypes.DB)}`Row`関数にも現れる。
型{anchorTerm RowStuck (module:=Examples.DependentTypes.DB)}`Row (c :: cs)`はどのデータ型にも簡約されない。{anchorName RowStuck (module:=Examples.DependentTypes.DB)}`Row`の定義が、単一要素のリストと、少なくとも二つの要素を持つリストの場合を分けているためである。
言い換えれば、変数{anchorName RowStuck (module:=Examples.DependentTypes.DB)}`cs`を具体的な{anchorName moreNames}`List`のコンストラクタにマッチさせようとして行き詰まる。
{anchorName RowStuck (module:=Examples.DependentTypes.DB)}`Row`を分解したり組み立てたりするほぼすべての関数が、{anchorName RowStuck (module:=Examples.DependentTypes.DB)}`Row`自体と同じ三つの場合にマッチさせる必要があるのはこのためである。行き詰まりを解くと、パターンマッチングにもコンストラクタにも使える具体的な型が現れる。

{anchorName appendL8}`appendL`の欠けている場合が要求するのは{lit}`Vect α (Nat.plusL n k + 1)`である。
添字にある{lit}`+ 1`は、次の段階が{anchorName consNotLengthN (module:=Examples.DependentTypes)}`Vect.cons`を使うことだと示唆している。
```anchor appendL8
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => ys
  | n + 1, k, .cons x xs, ys => .cons x (_ : Vect α (n.plusL k))
```
```anchorError appendL8
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α (n.plusL k)
```
{anchorName appendL9}`appendL`への再帰呼び出しで、望む長さの{anchorName appendL9}`Vect`を組み立てられる。

```anchor appendL9
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => ys
  | n + 1, k, .cons x xs, ys => .cons x (appendL n k xs ys)
```
プログラムが完成したので、{anchorName appendL9}`n`と{anchorName appendL9}`k`についての明示的なマッチングを取り除くと、読みやすく、関数を呼びやすくなる。

```anchor appendL
def appendL : Vect α n → Vect α k → Vect α (n.plusL k)
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (appendL xs ys)
```

定義上の等しさで型を比べるということは、関数の定義の中身を含め、定義上の等しさに関わるすべてが、依存型と添字付き族を使うプログラムの*インターフェース*の一部になるということである。
型に関数の中身をさらすということは、さらされたプログラムを書き換えると、それを使うプログラムが型検査を通らなくなることがあるということである。
特に、{anchorName appendL}`plusL`が{anchorName appendL}`appendL`の型に使われているということは、{anchorName appendL}`plusL`の定義を、それ以外は等価な{anchorName plusR}`plusR`に置き換えられないということである。

# 加法で行き詰まる
%%%
tag := "stuck-addition"
%%%

代わりに{anchorName appendR}`plusR`でappendを定義するとどうなるか。
同じように、長さを明示し、各場合に穴埋めのアンダースコアを置いて始めると、次の役に立つエラーメッセージが現れる。
```anchor appendR1
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => _
  | n + 1, k, .cons x xs, ys => _
```
```anchorError appendR1
don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α (Nat.plusR 0 k)
```
```anchorError appendR2
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α ((n + 1).plusR k)
```
しかし、一つ目の穴埋めに{anchorTerm appendR3}`Vect α k`の型注釈を付けようとすると、型の食い違いのエラーになる。
```anchor appendR3
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => _
```
```anchorError appendR3
Type mismatch
  ?m.11
has type
  Vect α k
but is expected to have type
  Vect α (Nat.plusR 0 k)
```
このエラーは、{anchorTerm plusRinfo}`Nat.plusR 0 k`と{anchorName plusRinfo}`k`が定義上等しく*ない*ことを指摘している。

:::paragraph
これは{anchorName plusR}`plusR`が次の定義を持つためである。

```anchor plusR
def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => plusR n k + 1
```
そのパターンマッチングは一つ目ではなく*二つ目*の引数について起きるので、その位置に変数{anchorName plusRinfo}`k`があると簡約できない。
Leanの標準ライブラリの{anchorName plusRinfo}`Nat.add`は{anchorName plusRinfo}`plusL`ではなく{anchorName plusRinfo}`plusR`と等価なので、これをこの定義で使おうとするとまったく同じ難点が生じる。
```anchor appendR4
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n + k)
  | 0, k, .nil, ys => (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => _
```
```anchorError appendR4
Type mismatch
  ?m.15
has type
  Vect α k
but is expected to have type
  Vect α (0 + k)
```

加法が変数で*行き詰まって*いる。
行き詰まりを解くには{ref "equality-and-ordering"}[命題としての等しさ]が要る。
:::

# 命題としての等しさ
%%%
tag := "propositional-equality"
%%%

命題としての等しさとは、二つの式が等しいという数学的な言明である。
定義上の等しさは、必要なときにLeanが自動で調べる、一種の周囲の事実であるが、命題としての等しさの言明には明示的な証明が要る。
等しさの命題が証明されれば、それをプログラムで使って型を変更し、等しさの一方の辺を他方で置き換えられ、型検査器の行き詰まりを解ける。

定義上の等しさがこれほど限られているのは、算法で調べられるようにするためである。
命題としての等しさはずっと豊かだが、計算機は一般に二つの式が命題として等しいかを調べられない。ただし、証明と言われているものが実際に証明であることは検証できる。
定義上の等しさと命題としての等しさの分かれ目は、人と機械の分業を表している。最も退屈な等しさは定義上の等しさの一部として自動で調べられ、人の頭は命題としての等しさにある興味深い問題に取り組める。
同様に、定義上の等しさは型検査器が自動で呼び出すが、命題としての等しさはわざわざ訴えねばならない。


{ref "props-proofs-indexing"}[命題・証明・添字付け]では、いくつかの等しさの言明を{tactic}`decide`で証明した。
これらの等しさの言明はすべて、命題としての等しさが実際にはすでに定義上の等しさであるものである。
通常、命題としての等しさの言明は、まず定義上等しいか、すでに証明された等しさに十分近い形にしてから、{tactic}`decide`や{tactic}`simp`のような道具で単純化した場合を片付けることで証明する。
{tactic}`simp`タクティクはかなり強力である。裏では多くの高速で自動の道具を使って証明を組み立てる。
{kw}`rfl`というより単純なタクティクは、定義上の等しさを使って命題としての等しさを証明する。
{kw}`rfl`という名前は*反射性*の略で、すべてのものがそれ自身に等しいという等しさの性質である。

{anchorName appendR}`appendR`の行き詰まりを解くには、{anchorTerm plusR_zero_left1}`k = Nat.plusR 0 k`の証明が要る。{anchorName plusR}`plusR`が二つ目の引数の変数で行き詰まっているので、これは定義上の等しさではない。
計算させるには、{anchorName plusR_zero_left1}`k`が具体的なコンストラクタにならねばならない。
これはパターンマッチングの仕事である。

:::paragraph
特に、{anchorName plusR_zero_left1}`k`が*どの*{anchorName plusR_zero_left1}`Nat`でもありうるので、この作業には、*どんな*{anchorName plusR_zero_left1}`k`についても{anchorTerm plusR_zero_left1}`k = Nat.plusR 0 k`の証拠を返せる関数が要る。
これは等しさの証明を返す関数で、型は{anchorTerm plusR_zero_left1}`(k : Nat) → k = Nat.plusR 0 k`であるべきである。
最初のパターンと穴埋めで始めると、次のメッセージが出る。
```anchor plusR_zero_left1
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => _
  | k + 1 => _
```
```anchorError plusR_zero_left1
don't know how to synthesize placeholder
context:
⊢ 0 = Nat.plusR 0 0
```
```anchorError plusR_zero_left2
don't know how to synthesize placeholder
context:
k : Nat
⊢ k + 1 = Nat.plusR 0 (k + 1)
```
パターンマッチングで{anchorName plusR_zero_left1}`k`を{anchorTerm plusR_zero_left1}`0`に洗練したので、一つ目の穴埋めは、定義上確かに成り立つ言明の証拠を表す。
{kw}`rfl`タクティクがそれを片付け、二つ目の穴埋めだけが残る。
```anchor plusR_zero_left3
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by rfl
  | k + 1 => _
```
:::

二つ目の穴埋めはもう少しやっかいである。
式{anchorTerm plusRStep}`Nat.plusR 0 k + 1`は{anchorTerm plusRStep}`Nat.plusR 0 (k + 1)`と定義上等しい。
つまりゴールは{anchorTerm plusR_zero_left4}`k + 1 = Nat.plusR 0 k + 1`とも書ける。
```anchor plusR_zero_left4
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by rfl
  | k + 1 => (_ : k + 1 = Nat.plusR 0 k + 1)
```
```anchorError plusR_zero_left4
don't know how to synthesize placeholder
context:
k : Nat
⊢ k + 1 = Nat.plusR 0 k + 1
```

:::paragraph
等しさの言明の両辺の{anchorTerm plusR_zero_left4}`+ 1`の下には、その関数自体が返すものの別の例がある。
言い換えれば、{anchorName plusR_zero_left4}`k`についての再帰呼び出しが{anchorTerm plusR_zero_left4}`k = Nat.plusR 0 k`の証拠を返す。
等しさが関数の引数に当てはまらないなら、等しさとは言えない。
言い換えれば、{anchorTerm congr}`x = y`なら{anchorTerm congr}`f x = f y`である。
標準ライブラリには、関数と等しさの証明を取り、等しさの両辺に関数を適用した新しい証明を返す{anchorName congr}`congrArg`関数がある。
この場合、その関数は{anchorTerm plusR_zero_left_done}`(· + 1)`である。

```anchor plusR_zero_left_done
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by rfl
  | k + 1 =>
    congrArg (· + 1) (plusR_zero_left k)
```
:::

:::paragraph
これは実際には命題の証明なので、{kw}`theorem`として宣言すべきである。

```anchor plusR_zero_left_thm
theorem plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by rfl
  | k + 1 =>
    congrArg (· + 1) (plusR_zero_left k)
```
:::

命題としての等しさは、右向きの三角の演算子{anchorTerm appendRsubst}`▸`を使ってプログラムで使える。
等しさの証明を一つ目の引数に、他の式を二つ目の引数に与えると、この演算子は二つ目の引数の型の中で、等しさの一方の辺の例を他方の辺で置き換える。
言い換えれば、次の定義には型エラーがない。
```anchor appendRsubst
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => plusR_zero_left k ▸ (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => _
```
一つ目の穴埋めは期待される型を持つ。
```anchorError appendRsubst
don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α k
```
これを{anchorName appendR5}`ys`で埋められる。
```anchor appendR5
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => plusR_zero_left k ▸ ys
  | n + 1, k, .cons x xs, ys => _
```

残りの穴埋めを埋めるには、加法の別の行き詰まりを解く必要がある。
```anchorError appendR5
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α ((n + 1).plusR k)
```
ここで証明すべき言明は{anchorTerm plusR_succ_left}`Nat.plusR (n + 1) k = Nat.plusR n k + 1`であり、これを{anchorTerm appendRsubst}`▸`とともに使うと、{anchorTerm appendRsubst}`+ 1`を式の一番上に引き出し、{anchorName Vect}`cons`の添字に一致させられる。

その証明は、{anchorName appendR}`plusR`の二つ目の引数、つまり{anchorName appendR5}`k`でパターンマッチングする再帰関数である。
{anchorName appendR5}`plusR`自体が二つ目の引数でパターンマッチングするので、その証明はパターンマッチングによって行き詰まりを「解き」、計算の振る舞いを明らかにできる。
その証明の骨組みは{anchorName appendR}`plusR_zero_left`のものとよく似ている。
```anchor plusR_succ_left_0
theorem plusR_succ_left (n : Nat) :
    (k : Nat) → Nat.plusR (n + 1) k = Nat.plusR n k + 1
  | 0 => by rfl
  | k + 1 => _
```

残りの場合の型は{anchorTerm congr}`Nat.plusR (n + 1) k + 1 = Nat.plusR n (k + 1) + 1`と定義上等しいので、{anchorName plusR_zero_left_thm}`plusR_zero_left`と同じく{anchorName congr}`congrArg`で解ける。
```anchorError plusR_succ_left_2
don't know how to synthesize placeholder
context:
n k : Nat
⊢ (n + 1).plusR (k + 1) = n.plusR (k + 1) + 1
```
これで証明が完成する。

```anchor plusR_succ_left
theorem plusR_succ_left (n : Nat) :
    (k : Nat) → Nat.plusR (n + 1) k = Nat.plusR n k + 1
  | 0 => by rfl
  | k + 1 => congrArg (· + 1) (plusR_succ_left n k)
```

完成した証明は、{anchorName appendR}`appendR`の二つ目の場合の行き詰まりを解くのに使える。

```anchor appendR
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys =>
    plusR_zero_left k ▸ ys
  | n + 1, k, .cons x xs, ys =>
    plusR_succ_left n k ▸ .cons x (appendR n k xs ys)
```
{anchorName appendR}`appendR`の長さの引数を再び暗黙にすると、証明で訴えるための名前が明示的にはなくなる。
しかし、型が一致するようにできる他の値がないので、Leanの型検査器は裏でそれらを自動で埋めるだけの情報を持っている。

```anchor appendRImpl
def appendR : Vect α n → Vect α k → Vect α (n.plusR k)
  | .nil, ys => plusR_zero_left _ ▸ ys
  | .cons x xs, ys => plusR_succ_left _ _ ▸ .cons x (appendR xs ys)
```

# 利点と欠点
%%%
tag := "dependent-types-pros-and-cons"
%%%

添字付き族には重要な性質がある。それについてのパターンマッチングが定義上の等しさに影響するのである。
たとえば、{anchorTerm Vect}`Vect`についての{kw}`match`式で{anchorName Vect}`nil`の場合、長さは単に{anchorTerm moreNames}`0`に*なる*。
定義上の等しさは常に働いており、明示的に呼び出す必要がないので、とても便利なことがある。

しかし、依存型とパターンマッチングとともに定義上の等しさを使うことには、ソフトウェア工学上の深刻な欠点がある。
第一に、関数は型で使えるように特別に書かねばならず、型で使いやすい関数が最も効率のよい算法を使っているとは限らない。
一度関数を型で使ってさらすと、その実装がインターフェースの一部になり、将来の書き換えが難しくなる。
第二に、定義上の等しさは遅くなりうる。
二つの式が定義上等しいかを調べるよう求められたとき、問題の関数が複雑で抽象の層が多いと、Leanは大量のコードを走らせねばならないことがある。
第三に、定義上の等しさが成り立たないために生じるエラーメッセージは、必ずしも理解しやすいとは限らない。関数の中身の言葉で述べられることがあるためである。
エラーメッセージにある式がどこから来たのかを理解するのは、必ずしも容易ではない。
最後に、自明でない不変条件を添字付き族と依存型の関数の集まりで符号化するのは、しばしば壊れやすい。
関数のさらされた簡約の振る舞いが便利な定義上の等しさを与えないと分かったときには、システムの初期の定義を変える必要がしばしば生じる。
代わりに、プログラムを等しさの証明への訴えで埋め尽くすこともできるが、それはかなり手に負えなくなりうる。

慣用的なLeanのコードでは、添字付きのデータ型はあまり使わない。
代わりに、重要な不変条件を強制するには部分型と明示的な命題を通常使う。
このやり方では多くの明示的な証明が関わり、定義上の等しさに訴えることはほとんどない。
対話的な定理証明器にふさわしく、Leanは明示的な証明を便利にするよう設計されている。
一般に、ほとんどの場合このやり方が好ましい。

しかし、データ型の添字付き族を理解することは重要である。
{anchorName plusR_zero_left_thm}`plusR_zero_left`や{anchorName plusR_succ_left}`plusR_succ_left`のような再帰関数は、実際には*数学的帰納法による証明*である。
再帰の基底の場合は帰納法の基底の場合に対応し、再帰呼び出しは帰納法の仮定への訴えを表す。
より一般に、Leanの新しい命題はしばしば証拠の帰納型として定義され、これらの帰納型は通常添字を持つ。
定理を証明する過程は、実際には裏でこれらの型を持つ式を組み立てることであり、その過程はこの節の証明によく似ている。
また、添字付きのデータ型がまさにその作業にぴったりの道具であることもある。
それらを使いこなせることは、いつ使うべきかを知るうえで重要な部分である。



# 練習問題
%%%
tag := "dependent-type-pitfalls-exercises"
%%%

 * {anchorName plusR_succ_left}`plusR_succ_left`の流儀の再帰関数を使って、すべての{anchorName moreNames}`Nat` {anchorName exercises}`n`と{anchorName exercises}`k`について{anchorTerm exercises}`n.plusR k = n + k`を証明せよ。
 * {anchorName moreNames}`Vect`上の関数で、{anchorName plusL}`plusL`を使うと定義に証明が必要になるが、{anchorName plusR}`plusR`のほうが自然なものを書け。
