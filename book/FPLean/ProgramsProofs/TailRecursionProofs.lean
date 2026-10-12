module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.TCO"

#doc (Manual) "Proving Equivalence" =>
%%%
tag := "proving-tail-rec-equiv"
%%%

末尾再帰とアキュムレータを使うように書き換えられたプログラムは、元のプログラムとかなり違って見えることがある。
元の再帰関数はずっと理解しやすいことが多いが、実行時にスタックを使い果たす危険がある。
単純な不具合を排除するために両方の版を例で試した後、証明を使えば、両者が等価であることを決定的に示せる。

# {lit}`sum`が等しいことの証明
%%%
tag := "proving-sum-equal"
%%%

{lit}`sum`の両方の版が等しいことを証明するには、まず定理の言明を仮の証明とともに書く。
```anchor sumEq0
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  skip
```
予想どおり、Leanは未解決のゴールを表示する。
```anchorError sumEq0
unsolved goals
⊢ NonTail.sum = Tail.sum
```

{anchorName sumEq0}`NonTail.sum`と{anchorName sumEq0}`Tail.sum`は定義上等しくないので、ここでは{kw}`rfl`タクティクを適用できない。
しかし、関数が等しくなる方法は定義上の等しさだけではない。
二つの関数が同じ入力に対して等しい出力を返すことを証明して、それらが等しいことを証明することもできる。
言い換えれば、ありとあらゆる入力$`x`について$`f(x) = g(x)`を証明すれば$`f = g`を証明できる。
この原理を*関数の外延性*と呼ぶ。
関数の外延性こそが、{anchorName sumEq0}`NonTail.sum`が{anchorName sumEq0}`Tail.sum`と等しい理由である。どちらも数のリストを足すからである。

Leanのタクティク言語では、関数の外延性は{anchorTerm sumEq1}`funext`で呼び出し、その後に任意の引数に使う名前を書く。
その任意の引数が文脈の前提として加えられ、ゴールは、その引数に関数を適用したものが等しいという証明を要求する形に変わる。
```anchor sumEq1
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
```
```anchorError sumEq1
unsolved goals
xs : List Nat
⊢ NonTail.sum xs = Tail.sum xs
```

このゴールは引数{anchorName sumEq1}`xs`についての帰納法で証明できる。
どちらの{lit}`sum`関数も空のリストに適用すると{anchorTerm TailSum}`0`を返し、これが基底の場合になる。
入力のリストの先頭に数を加えると、どちらの関数もその数を結果に加え、これが帰納法の段階になる。
{anchorTerm sumEq2a}`induction`タクティクを呼び出すと、二つのゴールになる。
```anchor sumEq2a
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => skip
  | cons y ys ih => skip
```
```anchorError sumEq2a
unsolved goals
case nil
⊢ NonTail.sum [] = Tail.sum []
```
```anchorError sumEq2b
unsolved goals
case cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ NonTail.sum (y :: ys) = Tail.sum (y :: ys)
```

{anchorName sumEq3}`nil`の基底の場合は{anchorTerm sumEq3}`rfl`で解ける。どちらの関数も空のリストを渡すと{anchorTerm TailSum}`0`を返すためである。
```anchor sumEq3
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys ih => skip
```

帰納法の段階を解く最初の段階は、ゴールを単純化し、{anchorTerm sumEq4}`simp`に{anchorName sumEq4}`NonTail.sum`と{anchorName sumEq4}`Tail.sum`を展開させることである。
```anchor sumEq4
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp [NonTail.sum, Tail.sum]
```
```anchorError sumEq4
unsolved goals
case cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ y + NonTail.sum ys = Tail.sumHelper 0 (y :: ys)
```
{anchorName sumEq5}`Tail.sum`を展開すると、それがすぐに{anchorName sumEq5}`Tail.sumHelper`に委ねていることが分かるので、これも単純化すべきである。
```anchor sumEq5
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp [NonTail.sum, Tail.sum, Tail.sumHelper]
```
その結果のゴールでは、{anchorName TailSum}`sumHelper`が計算を一段階進め、{anchorName sumEq5}`y`をアキュムレータに加えている。
```anchorError sumEq5
unsolved goals
case cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ y + NonTail.sum ys = Tail.sumHelper y ys
```
帰納法の仮定で書き換えると、ゴールから{anchorName sumEq6}`NonTail.sum`の記述がすべて消える。
```anchor sumEq6
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp [NonTail.sum, Tail.sum, Tail.sumHelper]
    rw [ih]
```
```anchorError sumEq6
unsolved goals
case cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ y + Tail.sum ys = Tail.sumHelper y ys
```
この新しいゴールは、リストの和に数を加えることが、その数を{anchorName TailSum}`sumHelper`の初期のアキュムレータとして使うことと同じであることを述べている。
分かりやすさのため、この新しいゴールは別の定理として証明できる。
```anchor sumEqHelperBad0
theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
    n + Tail.sum xs = Tail.sumHelper n xs := by
  skip
```
```anchorError sumEqHelperBad0
unsolved goals
xs : List Nat
n : Nat
⊢ n + Tail.sum xs = Tail.sumHelper n xs
```
ここでもまた、基底の場合に{anchorTerm sumEqHelperBad1}`rfl`を使う帰納法による証明である。
```anchor sumEqHelperBad1
theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
    n + Tail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih => skip
```
```anchorError sumEqHelperBad1
unsolved goals
case cons
n y : Nat
ys : List Nat
ih : n + Tail.sum ys = Tail.sumHelper n ys
⊢ n + Tail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
```
これは帰納法の段階なので、帰納法の仮定{anchorName sumEqHelperBad2}`ih`に一致するまでゴールを単純化すべきである。
{anchorName sumEqHelperBad2}`Tail.sum`と{anchorName sumEqHelperBad2}`Tail.sumHelper`の定義を使って単純化すると次のようになる。
```anchor sumEqHelperBad2
theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
    n + Tail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp [Tail.sum, Tail.sumHelper]
```
```anchorError sumEqHelperBad2
unsolved goals
case cons
n y : Nat
ys : List Nat
ih : n + Tail.sum ys = Tail.sumHelper n ys
⊢ n + Tail.sumHelper y ys = Tail.sumHelper (y + n) ys
```
理想的には、帰納法の仮定を使って{lit}`Tail.sumHelper (y + n) ys`を置き換えたいところだが、一致しない。
帰納法の仮定は{lit}`Tail.sumHelper n ys`には使えるが、{lit}`Tail.sumHelper (y + n) ys`には使えない。
言い換えれば、この証明は行き詰まっている。

# 二度目の試み
%%%
tag := "proving-sum-equal-again"
%%%

証明をでたらめに進めようとするより、一歩引いて考える時である。
なぜ末尾再帰の版の関数が末尾再帰でない版と等しいのか。
根本的に言えば、リストの各要素で、アキュムレータは再帰の結果に加えられるはずの量と同じだけ増える。
この洞察を使えば、優雅な証明が書ける。
決定的に重要なのは、帰納法の仮定を*どの*アキュムレータの値にも適用できるように、帰納法による証明を組み立てることである。

先ほどの試みを捨て、その洞察を次の言明として符号化できる。
```anchor nonTailEqHelper0
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  skip
```
この言明では、{anchorName nonTailEqHelper0}`n`がコロンの後の型の一部であることが非常に重要である。
得られるゴールは{lit}`∀ (n : Nat)`で始まり、これは「すべての{lit}`n`について」の略である。
```anchorError nonTailEqHelper0
unsolved goals
xs : List Nat
⊢ ∀ (n : Nat), n + NonTail.sum xs = Tail.sumHelper n xs
```
帰納法のタクティクを使うと、この「すべての」という言明を含むゴールになる。
```anchor nonTailEqHelper1a
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => skip
  | cons y ys ih => skip
```
{anchorName nonTailEqHelper1a}`nil`の場合、ゴールは次のとおりである。
```anchorError nonTailEqHelper1a
unsolved goals
case nil
⊢ ∀ (n : Nat), n + NonTail.sum [] = Tail.sumHelper n []
```
{anchorName nonTailEqHelper1a}`cons`の帰納法の段階では、帰納法の仮定と個別のゴールの両方に「すべての{lit}`n`」が含まれる。
```anchorError nonTailEqHelper1b
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
⊢ ∀ (n : Nat), n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
```
言い換えれば、ゴールは証明するのがより難しくなったが、それに対応して帰納法の仮定がより役に立つものになっている。

「すべての$`x`について」で始まる言明の数学的な証明では、任意の$`x`を仮定してその言明を証明すべきである。
「任意」とは、$`x`について追加の性質を仮定しないということであり、得られる言明は*どの*$`x`でも成り立つ。
Leanでは、「すべての」という言明は依存関数である。どの具体的な値に適用しても、その命題の証拠を返す。
同様に、任意の$`x`を選ぶ過程は{lit}`fun x => ...`を使うのと同じである。
タクティク言語では、この任意の$`x`を選ぶ過程は{kw}`intro`タクティクで行い、タクティクの筋書きが終わったときに裏でその関数を作る。
{kw}`intro`タクティクには、この任意の値に使う名前を与えるべきである。

{anchorName nonTailEqHelper2}`nil`の場合に{kw}`intro`タクティクを使うと、ゴールから{lit}`∀ (n : Nat),`が消え、前提{lit}`n : Nat`が加わる。
```anchor nonTailEqHelper2
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => intro n
  | cons y ys ih => skip
```
```anchorError nonTailEqHelper2
unsolved goals
case nil
n : Nat
⊢ n + NonTail.sum [] = Tail.sumHelper n []
```
この命題としての等しさの両辺は{anchorName nonTailEqHelper3}`n`と定義上等しいので、{anchorTerm nonTailEqHelper3}`rfl`で足りる。
```anchor nonTailEqHelper3
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih => skip
```
{anchorName nonTailEqHelper3}`cons`のゴールにも「すべての」が含まれる。
```anchorError nonTailEqHelper3
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
⊢ ∀ (n : Nat), n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
```
これは{kw}`intro`を使うことを示唆している。
```anchor nonTailEqHelper4
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
```
```anchorError nonTailEqHelper4
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
```
証明のゴールには、{lit}`y :: ys`に適用された{anchorName nonTailEqHelper5}`NonTail.sum`と{anchorName nonTailEqHelper5}`Tail.sumHelper`の両方が含まれる。
単純化器を使うと次の段階がより明確になる。
```anchor nonTailEqHelper5
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
```
```anchorError nonTailEqHelper5
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ n + (y + NonTail.sum ys) = Tail.sumHelper (y + n) ys
```
このゴールは帰納法の仮定にほとんど一致している。
一致しない点が二つある。
 * 等式の左辺は{lit}`n + (y + NonTail.sum ys)`だが、帰納法の仮定は左辺が{lit}`NonTail.sum ys`に数を加えたものであることを要求する。
   言い換えれば、このゴールは{lit}`(n + y) + NonTail.sum ys`に書き換えるべきであり、自然数の加法が結合的であるのでこれは妥当である。
 * 左辺を{lit}`(y + n) + NonTail.sum ys`に書き換えたとき、一致させるには右辺のアキュムレータの引数が{lit}`y + n`ではなく{lit}`n + y`であるべきである。
   加法は可換でもあるので、この書き換えは妥当である。

加法の結合性と可換性はすでにLeanの標準ライブラリで証明されている。
結合性の証明は{anchorTerm NatAddAssoc}`Nat.add_assoc`という名前で、型は{anchorTerm NatAddAssoc}`(n m k : Nat) → (n + m) + k = n + (m + k)`であり、可換性の証明は{anchorTerm NatAddComm}`Nat.add_comm`と呼ばれ、型は{anchorTerm NatAddComm}`(n m : Nat) → n + m = m + n`である。
通常、{kw}`rw`タクティクには型が等しさである式を与える。
しかし、引数が代わりに戻り値の型が等しさである依存関数なら、その等しさがゴールの中の何かに一致するようにする関数の引数を見つけようとする。
結合性を適用する機会は一つだけだが、{anchorTerm NatAddAssoc}`(n + m) + k = n + (m + k)`の等しさの右辺が証明のゴールに一致するので、書き換えの向きは逆にせねばならない。
```anchor nonTailEqHelper6
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [←Nat.add_assoc]
```
```anchorError nonTailEqHelper6
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ n + y + NonTail.sum ys = Tail.sumHelper (y + n) ys
```
しかし、{anchorTerm nonTailEqHelper7}`rw [Nat.add_comm]`で直接書き換えると、間違った結果になる。
{kw}`rw`タクティクが書き換えの場所を間違って推測し、意図しないゴールになる。
```anchor nonTailEqHelper7
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [←Nat.add_assoc]
    rw [Nat.add_comm]
```
```anchorError nonTailEqHelper7
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ NonTail.sum ys + (n + y) = Tail.sumHelper (y + n) ys
```
これは{anchorName nonTailEqHelper8}`Nat.add_comm`の引数として{anchorName nonTailEqHelper8}`y`と{anchorName nonTailEqHelper8}`n`を明示的に与えれば直せる。
```anchor nonTailEqHelper8
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [←Nat.add_assoc]
    rw [Nat.add_comm y n]
```
```anchorError nonTailEqHelper8
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ n + y + NonTail.sum ys = Tail.sumHelper (n + y) ys
```
これでゴールが帰納法の仮定に一致する。
特に、帰納法の仮定の型は依存関数型である。
{anchorName nonTailEqHelperDone}`ih`を{anchorTerm nonTailEqHelperDone}`n + y`に適用すると、まさに望む型になる。
{kw}`exact`タクティクは、その引数がまさに望む型を持つときに証明のゴールを完成させる。

```anchor nonTailEqHelperDone
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => intro n; rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [←Nat.add_assoc]
    rw [Nat.add_comm y n]
    exact ih (n + y)
```

実際の証明では、ゴールを補助関数の型に一致させるのに少し手間が増えるだけである。
最初の段階はやはり関数の外延性を呼び出すことである。
```anchor nonTailEqReal0
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
```
```anchorError nonTailEqReal0
unsolved goals
xs : List Nat
⊢ NonTail.sum xs = Tail.sum xs
```
次の段階は{anchorName nonTailEqReal1}`Tail.sum`を展開し、{anchorName TailSum}`Tail.sumHelper`を現すことである。
```anchor nonTailEqReal1
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  simp [Tail.sum]
```
```anchorError nonTailEqReal1
unsolved goals
xs : List Nat
⊢ NonTail.sum xs = Tail.sumHelper 0 xs
```
これをすると、型はほとんど一致する。
しかし、補助関数は左辺に加数が一つ余分にある。
言い換えれば、証明のゴールは{lit}`NonTail.sum xs = Tail.sumHelper 0 xs`だが、{anchorName nonTailEqHelper0}`non_tail_sum_eq_helper_accum`を{anchorName nonTailEqReal2}`xs`と{anchorTerm NatZeroAdd}`0`に適用すると型{lit}`0 + NonTail.sum xs = Tail.sumHelper 0 xs`になる。
もう一つの標準ライブラリの証明{anchorTerm NatZeroAdd}`Nat.zero_add`は型{anchorTerm NatZeroAdd}`(n : Nat) → 0 + n = n`を持つ。
この関数を{anchorTerm nonTailEqReal2}`NonTail.sum xs`に適用すると、型{anchorTerm NatZeroAddApplied}`0 + NonTail.sum xs = NonTail.sum xs`の式になるので、右から左へ書き換えると望むゴールになる。
```anchor nonTailEqReal2
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  simp [Tail.sum]
  rw [←Nat.zero_add (NonTail.sum xs)]
```
```anchorError nonTailEqReal2
unsolved goals
xs : List Nat
⊢ 0 + NonTail.sum xs = Tail.sumHelper 0 xs
```
最後に、補助関数を使って証明を完成させられる。

```anchor nonTailEqRealDone
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  simp [Tail.sum]
  rw [←Nat.zero_add (NonTail.sum xs)]
  exact non_tail_sum_eq_helper_accum xs 0
```

この証明は、アキュムレータを渡す末尾再帰関数が末尾再帰でない版と等しいことを証明するときに使える一般的なパターンを示している。
最初の段階は、開始時のアキュムレータの引数と最終的な結果の関係を見つけることである。
たとえば、{anchorName TailSum}`Tail.sumHelper`をアキュムレータ{anchorName accum_stmt}`n`で始めると、最終的な和が{anchorName accum_stmt}`n`に加えられ、{anchorName accum_stmt}`Tail.reverseHelper`をアキュムレータ{anchorName accum_stmt}`ys`で始めると、最終的に反転したリストが{anchorName accum_stmt}`ys`の前に付けられる。
第二の段階は、この関係を定理の言明として書き、帰納法で証明することである。
実際にはアキュムレータは常に{anchorTerm TailSum}`0`や{anchorTerm accum_stmt}`[]`のような中立の値で初期化されるが、開始時のアキュムレータをどの値でもよいとするこのより一般的な言明こそが、十分に強い帰納法の仮定を得るのに必要なものである。
最後に、この補助定理を実際の初期のアキュムレータの値とともに使うと、望む証明になる。
たとえば{anchorName nonTailEqRealDone}`non_tail_sum_eq_tail_sum`では、アキュムレータは{anchorTerm TailSum}`0`と指定されている。
これには、中立の初期のアキュムレータの値が正しい場所に現れるようにゴールを書き換える必要が生じることがある。

# 関数による帰納法
%%%
tag := "fun-induction"
%%%

{anchorName nonTailEqRealDone}`non_tail_sum_eq_helper_accum`の証明は{anchorName TailSum}`Tail.sumHelper`の実装をよく追っている。
しかし、その実装と数学的帰納法が期待する構造は完全には一致せず、仮定{anchorName nonTailEqHelperDone}`n`を注意深く扱う必要がある。
{anchorName nonTailEqHelperDone}`non_tail_sum_eq_helper_accum`の場合は手間は少しで済むが、定義が{tactic}`induction`の期待する構造から遠い関数についての証明では、より多くの帳尻合わせが要る。

再帰関数についての定理を引数の一つについての帰納法で証明するのに加えて、Leanは関数の再帰呼び出しの構造についての帰納法による証明を支える。
この{deftech}*関数による帰納法*では、その関数の制御の流れのうち再帰呼び出しを含まない枝ごとに基底の場合が得られ、含む枝ごとに帰納法の段階が得られる。
関数による帰納法による証明では、再帰でない枝について定理が成り立つことと、各再帰呼び出しの結果について定理が成り立つなら再帰の枝の結果についても成り立つことを示すべきである。

:::paragraph
関数による帰納法を使うと{anchorName nonTailEqHelperFunInd1}`non_tail_sum_eq_helper_accum`が簡単になる。
```anchor nonTailEqHelperFunInd1
theorem non_tail_sum_eq_helper_accum (xs : List Nat) (n : Nat) :
    n + NonTail.sum xs = Tail.sumHelper n xs := by
  fun_induction Tail.sumHelper with
  | case1 n => skip
  | case2 n y ys ih => skip
```
証明の各枝は{anchorName TailSum}`Tail.sumHelper`の対応する枝に一致する。
```anchorTerm TailSum
def Tail.sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs
```
一つ目の{anchorTerm nonTailEqHelperFunInd1}`case1`では、等しさの右辺がアキュムレータの値であり、証明では{anchorName nonTailEqHelperFunInd1}`n`と呼ばれる。
```anchorError nonTailEqHelperFunInd1
unsolved goals
case case1
n : Nat
⊢ n + NonTail.sum [] = n
```
二つ目の{anchorTerm nonTailEqHelperFunInd1}`case2`では、等しさの右辺が末尾再帰のループの次の段階である。
```anchorError nonTailEqHelperFunInd1
unsolved goals
case case2
n y : Nat
ys : List Nat
ih : y + n + NonTail.sum ys = Tail.sumHelper (y + n) ys
⊢ n + NonTail.sum (y :: ys) = Tail.sumHelper (y + n) ys
```
:::

:::paragraph
得られる証明はより簡単にできる。
使う加法の性質を含め、議論の根本は同じであるが、帳尻合わせが取り除かれている。
アキュムレータの値を手でやりくりする必要がなくなり、帰納法の仮定を具体化せずに直接使える。
```anchor nonTailEqHelperFunInd2
theorem non_tail_sum_eq_helper_accum (xs : List Nat) (n : Nat) :
    n + NonTail.sum xs = Tail.sumHelper n xs := by
  fun_induction Tail.sumHelper with
  | case1 n => simp [NonTail.sum]
  | case2 n y ys ih =>
    simp [NonTail.sum]
    rw [←Nat.add_assoc]
    rw [Nat.add_comm n y]
    assumption
```
:::

:::paragraph
{tactic}`grind`タクティクはこの種のゴールによく合っている。
{tactic}`simp`や{tactic}`rw`と違い、向きを持たない。内部的には、ゴールを完全に証明するか失敗するまで、事実の集まりを蓄積する。
加法の結合性や可換性のような算術の基本的な事実を使うようあらかじめ設定されており、帰納法の仮定のような局所的な前提を自動で使う。
{tactic}`grind`を使うと、この証明は短く要点を突いたものになる。
```anchor nonTailEqHelperFunInd3
theorem non_tail_sum_eq_helper_accum (xs : List Nat) (n : Nat) :
    n + NonTail.sum xs = Tail.sumHelper n xs := by
  fun_induction Tail.sumHelper <;> grind [NonTail.sum]
```
この証明は、熟練したプログラマに証明を説明するときの言い方とも合っている。「{anchorName nonTailEqHelperFunInd3}`Tail.sumHelper`の両方の枝を調べればよいだけだ」と言えばよい。
:::

# 練習問題
%%%
tag := "tail-recursion-proof-exercises"
%%%

## 肩慣らし
%%%
tag := none
%%%

{anchorName NatZeroAdd}`Nat.zero_add`、{anchorName NatAddAssoc}`Nat.add_assoc`、{anchorName NatAddComm}`Nat.add_comm`の証明を、{kw}`induction`タクティクを使って自分で書け。

## アキュムレータについてのさらなる証明
%%%
tag := none
%%%

### リストの反転
%%%
tag := none
%%%

{anchorName NonTailSum}`sum`の証明を、{anchorName NonTailReverse}`NonTail.reverse`と{anchorName TailReverse}`Tail.reverse`の証明に合わせよ。
まず、{anchorName TailReverse}`Tail.reverseHelper`に渡されるアキュムレータの値と、末尾再帰でない反転の関係を考える。
{anchorName TailSum}`Tail.sumHelper`でアキュムレータに数を加えるのが全体の和にそれを加えるのと同じであるように、{anchorName TailReverse}`Tail.reverseHelper`で{anchorName names}`List.cons`を使ってアキュムレータに新しい要素を加えるのは、全体の結果への何らかの変更に相当する。
紙と鉛筆で三つか四つの違うアキュムレータの値を試し、関係がはっきりするまで考えよ。
この関係を使って、適切な補助定理を証明せよ。
この補助定理を、リストについての帰納法と関数による帰納法の両方で証明してみよ。
次に、全体の定理を書き下せ。
{anchorName reverseEqStart}`NonTail.reverse`と{anchorName TailReverse}`Tail.reverse`は多相なので、それらの等しさを述べるには{lit}`@`を使って、{anchorName reverseEqStart}`α`にどの型を使うかをLeanが考えようとするのを止める必要がある。
{anchorName reverseEqStart}`α`を普通の引数として扱えば、{kw}`funext`は{anchorName reverseEqStart}`α`と{anchorName reverseEqStart}`xs`の両方とともに呼び出すべきである。
```anchor reverseEqStart
theorem non_tail_reverse_eq_tail_reverse :
    @NonTail.reverse = @Tail.reverse := by
  funext α xs
```
これで適切なゴールになる。
```anchorError reverseEqStart
unsolved goals
α : Type u_1
xs : List α
⊢ NonTail.reverse xs = Tail.reverse xs
```


### 階乗
%%%
tag := none
%%%


前の節の練習問題の{anchorName NonTailFact}`NonTail.factorial`が、自分の末尾再帰の解答と等しいことを、アキュムレータと結果の関係を見つけて適切な補助定理を証明することで証明せよ。
