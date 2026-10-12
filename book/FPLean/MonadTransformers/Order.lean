module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.MonadTransformers.Defs"

#doc (Manual) "Ordering Monad Transformers" =>
%%%
tag := "monad-transformer-order"
%%%

モナド変換子の積み重ねからモナドを組み立てるときは、モナド変換子を重ねる順序が重要であることに注意すべきである。
同じ変換子の組でも順序が違えば異なるモナドになる。

この{anchorName countLettersClassy}`countLetters`の版は、具体的なモナドを与える代わりに、使える副作用の組を型クラスで記述する点を除けば、前の版と同じである。

```anchor countLettersClassy
def countLetters [Monad m] [MonadState LetterCounts m] [MonadExcept Err m]
    (str : String) : m Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        else -- modified or non-English letter
          pure ()
      else throw (.notALetter c)
      loop cs
  loop str.toList
```
状態と例外のモナド変換子は二通りの順序で組み合わせられ、どちらも両方の型クラスのインスタンスを持つモナドになる。

```anchor SomeMonads
abbrev M1 := StateT LetterCounts (ExceptT Err Id)
abbrev M2 := ExceptT Err (StateT LetterCounts Id)
```

プログラムが例外を投げない入力で実行すると、どちらのモナドも似た結果になる。
```anchor countLettersM1Ok
#eval countLetters (m := M1) "hello" ⟨0, 0⟩
```
```anchorInfo countLettersM1Ok
Except.ok ((), { vowels := 2, consonants := 3 })
```
```anchor countLettersM2Ok
#eval countLetters (m := M2) "hello" ⟨0, 0⟩
```
```anchorInfo countLettersM2Ok
(Except.ok (), { vowels := 2, consonants := 3 })
```
しかし、これらの戻り値には細かな違いがある。
{anchorName M1eval}`M1`の場合は、最も外側のコンストラクタが{anchorName MonadExceptT}`Except.ok`であり、その中にunitのコンストラクタと最終状態の組が入っている。
{anchorName M2eval}`M2`の場合は、最も外側のコンストラクタが組であり、その中にunitのコンストラクタだけに適用された{anchorName MonadExceptT}`Except.ok`が入っている。
最終状態は{anchorName MonadExceptT}`Except.ok`の外側にある。
どちらの場合も、プログラムは母音と子音の数を返す。

一方、文字列が例外を引き起こすときは、母音と子音の数を返すのは一方のモナドだけである。
{anchorName M1eval}`M1`を使うと、例外の値だけが返る。
```anchor countLettersM1Error
#eval countLetters (m := M1) "hello!" ⟨0, 0⟩
```
```anchorInfo countLettersM1Error
Except.error (StEx.Err.notALetter '!')
```
{anchorName SomeMonads}`M2`を使うと、例外の値が、例外が投げられた時点の状態と組になる。
```anchor countLettersM2Error
#eval countLetters (m := M2) "hello!" ⟨0, 0⟩
```
```anchorInfo countLettersM2Error
(Except.error (StEx.Err.notALetter '!'), { vowels := 2, consonants := 3 })
```

{anchorName SomeMonads}`M2`のほうが、デバッグに役立ちうる情報を多く与えるので{anchorName SomeMonads}`M1`より優れている、と考えたくなるかもしれない。
同じプログラムが{anchorName SomeMonads}`M1`と{anchorName SomeMonads}`M2`で*違う*答えを計算することがあり、どちらかの答えが必ず優れていると言える原理的な理由はない。
これは、例外を扱う段階をプログラムに加えると分かる。

```anchor countWithFallback
def countWithFallback
    [Monad m] [MonadState LetterCounts m] [MonadExcept Err m]
    (str : String) : m Unit :=
  try
    countLetters str
  catch _ =>
    countLetters "Fallback"
```
このプログラムは常に成功するが、その成功の結果は異なりうる。
例外が投げられなければ、結果は{anchorName countWithFallback}`countLetters`と同じである。
```anchor countWithFallbackM1Ok
#eval countWithFallback (m := M1) "hello" ⟨0, 0⟩
```
```anchorInfo countWithFallbackM1Ok
Except.ok ((), { vowels := 2, consonants := 3 })
```
```anchor countWithFallbackM2Ok
#eval countWithFallback (m := M2) "hello" ⟨0, 0⟩
```
```anchorInfo countWithFallbackM2Ok
(Except.ok (), { vowels := 2, consonants := 3 })
```
しかし、例外が投げられて捕まえられると、最終状態は大きく異なる。
{anchorName countWithFallbackM1Error}`M1`では、最終状態に{anchorTerm countWithFallback}`"Fallback"`の文字の数だけが入る。
```anchor countWithFallbackM1Error
#eval countWithFallback (m := M1) "hello!" ⟨0, 0⟩
```
```anchorInfo countWithFallbackM1Error
Except.ok ((), { vowels := 2, consonants := 6 })
```
{anchorName countWithFallbackM2Error}`M2`では、命令型言語で期待されるように、最終状態に{anchorTerm countWithFallbackM2Error}`"hello!"`と{anchorTerm countWithFallback}`"Fallback"`の両方の文字の数が入る。
```anchor countWithFallbackM2Error
#eval countWithFallback (m := M2) "hello!" ⟨0, 0⟩
```
```anchorInfo countWithFallbackM2Error
(Except.ok (), { vowels := 4, consonants := 9 })
```

{anchorName countWithFallbackM1Error}`M1`では、例外を投げると状態が例外を捕まえた時点まで「巻き戻る」。
{anchorName countLettersM2Error}`M2`では、状態への変更が例外の送出と捕捉をまたいで残る。
この違いは、{anchorName SomeMonads}`M1`と{anchorName SomeMonads}`M2`の定義を展開すると分かる。
{anchorTerm M1eval}`M1 α`は{anchorTerm M1eval}`LetterCounts → Except Err (α × LetterCounts)`に展開され、{anchorTerm M2eval}`M2 α`は{anchorTerm M2eval}`LetterCounts → Except Err α × LetterCounts`に展開される。
つまり、{anchorTerm M1eval}`M1 α`は初期の文字の数を取り、エラーか、更新された数と組になった{anchorName M1eval}`α`を返す関数を記述する。
{anchorName M1eval}`M1`で例外が投げられると、最終状態はない。
{anchorTerm M2eval}`M2 α`は、初期の文字の数を取り、エラーか{anchorName M2eval}`α`と組になった新しい文字の数を返す関数を記述する。
{anchorName M2eval}`M2`で例外が投げられると、それには状態が付き添う。

# モナドの可換性
%%%
tag := "commuting-monads"
%%%

関数型プログラミングの言葉では、二つのモナド変換子は、プログラムの意味を変えずに順序を入れ替えられるときに*可換*であるという。
{anchorName SomeMonads}`StateT`と{anchorName SomeMonads}`ExceptT`の順序を入れ替えるとプログラムの結果が変わりうるということは、状態と例外が可換でないことを意味する。
一般に、モナド変換子が可換であることは期待すべきでない。

すべてのモナド変換子が可換なわけではないが、可換なものもある。
たとえば、{anchorName SomeMonads}`StateT`を二つ使う場合は順序を入れ替えられる。
{anchorTerm StateTDoubleA}`StateT σ (StateT σ' Id) α`の定義を展開すると型{anchorTerm StateTDoubleA}`σ → σ' → ((α × σ) × σ')`になり、{anchorTerm StateTDoubleB}`StateT σ' (StateT σ Id) α`は{anchorTerm StateTDoubleB}`σ' → σ → ((α × σ') × σ)`になる。
言い換えれば、両者の違いは、戻り値の型の中で{anchorName StateTDoubleA}`σ`と{anchorName StateTDoubleA}`σ'`の型を入れ子にする場所が違うことと、引数を受け取る順序が違うことである。
利用側のコードは同じ入力を与える必要があり、同じ出力を受け取ることになる。

可変状態と例外の両方を持つほとんどのプログラミング言語は{anchorName SomeMonads}`M2`のように働く。
それらの言語では、例外が投げられたときに巻き戻す*べき*状態を表すのは難しく、通常は{anchorName SomeMonads}`M1`で明示的に状態の値を受け渡すのによく似たやり方でまねる必要がある。
モナド変換子は、目の前の問題に合う副作用の順序の解釈を選ぶ自由を与え、どちらの選択も同じくらい容易にプログラミングできる。
しかし、変換子の順序の選択には注意も要る。
大きな表現力には、表現しているものが意図したものであるかを確かめる責任が伴う。{anchorName countWithFallback}`countWithFallback`の型シグネチャは、おそらくあるべき以上に多相的である。


# 練習問題
%%%
tag := "monad-transformer-order-exercises"
%%%

 * {anchorName m}`ReaderT`と{anchorName SomeMonads}`StateT`が可換であることを、定義を展開して得られる型について推論して確かめよ。
 * {anchorName m}`ReaderT`と{anchorName SomeMonads}`ExceptT`は可換か。定義を展開して得られる型について推論し、答えを確かめよ。
 * {anchorName Many (module:=Examples.Monads.Many)}`Many`の定義に基づいてモナド変換子{lit}`ManyT`を、適切な{anchorName AlternativeOptionT}`Alternative`インスタンスとともに構成せよ。それが{anchorName AlternativeOptionT}`Monad`の契約を満たすことを確かめよ。
 * {lit}`ManyT`は{anchorName SomeMonads}`StateT`と可換か。可換なら、定義を展開して得られる型について推論し、答えを確かめよ。可換でないなら、{lit}`ManyT (StateT σ Id)`のプログラムと{lit}`StateT σ (ManyT Id)`のプログラムを書け。それぞれ、そのモナド変換子の順序のほうがよく合うプログラムとする。
