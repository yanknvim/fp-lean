module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

#doc (Manual) "Next Steps" =>
%%%
tag := "next-steps"
htmlSplit := .never
%%%

この本は、Leanでの関数型プログラミングのごく基本を、わずかな対話的な定理証明も含めて紹介した。
Leanのような依存型を持つ関数型言語を使いこなすのは深い話題であり、語るべきことは多い。
興味に応じて、Lean 4を学ぶのに次の資料が役に立つかもしれない。

# Leanを学ぶ
%%%
tag := "learning-lean"
%%%

Lean 4自体は次の資料で説明されている。

 * [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)はLeanで証明を書くための入門書である。
 * [The Lean 4 Manual](https://lean-lang.org/doc/reference/latest/)は言語とその機能の詳しい説明を与える。
 * [How To Prove It With Lean](https://djvelleman.github.io/HTPIwL/)は、紙と鉛筆で数学の証明を書くための入門を与える定評ある教科書[_How To Prove It_](https://www.cambridge.org/highereducation/books/how-to-prove-it/6D2965D625C6836CD4A785A2C843B3DA)に合わせたLean版の副読本である。
 * [Metaprogramming in Lean 4](https://github.com/arthurpaulino/lean4-metaprogramming-book)は、中置演算子や記法からマクロ、独自のタクティク、本格的な独自の埋め込み言語まで、Leanの拡張の仕組みを概観する。
 * [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)は、再帰についての冗談を好む読者に面白いかもしれない。

しかし、Leanの学習を続ける最良の方法は、コードを読み書きし始め、行き詰まったときに資料を参照することである。
さらに、[Lean Zulip](https://leanprover.zulipchat.com/)は、他のLeanの利用者と出会い、助けを求め、他の人を助けるのに絶好の場である。

# Leanでの数学
%%%
tag := none
%%%

数学者向けの学習資料が[コミュニティのサイト](https://leanprover-community.github.io/learn.html)に豊富にそろっている。

# 計算機科学で依存型を使う
%%%
tag := none
%%%

RocqはLeanと多くの共通点を持つ言語である。
計算機科学者には、対話的な教科書の[Software Foundations](https://softwarefoundations.cis.upenn.edu/)シリーズが、計算機科学でのRocqの応用への優れた入門を与える。
LeanとRocqの基本的な考え方は非常によく似ており、技能は両者の間で容易に移せる。

# 依存型を使ったプログラミング
%%%
tag := none
%%%

添字付き族と依存型を使ってプログラムを組み立てることを学びたいプログラマには、Edwin Bradyの[_Type Driven Development with Idris_](https://www.manning.com/books/type-driven-development-with-idris)が優れた入門を与える。
Rocqと同じく、IdrisはLeanの近い親戚であるが、タクティクを欠いている。

# 依存型を理解する
%%%
tag := none
%%%

[_The Little Typer_](https://thelittletyper.com/)は、論理学やプログラミング言語の理論を正式に学んだことはないが、依存型理論の核となる考え方を理解したいプログラマ向けの本である。
上記の資料はどれもできるだけ実用的であろうとしているが、_The Little Typer_は、プログラミングの概念だけを使ってごく基本から積み上げる、依存型理論への一つの取り組み方を示している。
注意: _Functional Programming in Lean_の著者は_The Little Typer_の著者でもある。
