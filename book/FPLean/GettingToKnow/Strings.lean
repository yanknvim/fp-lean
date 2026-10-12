module
public import VersoManual
import FPLean.Examples



open Verso.Genre Manual
open Verso Code External

open FPLean
example_module Examples.Strings

set_option verso.exampleProject "../examples"

set_option verso.exampleModule "Examples.Strings"

#doc (Manual) "Characters, Strings, and Slices" =>
%%%
tag := "chars-strings-slices"
%%%

Leanでは、文字列はUnicodeのテキストを入れる。
正確には、文字列は文字の並びであり、文字はUnicodeのコードポイントである。
文字列は二重引用符で、個々の文字は単一引用符で書く。
文字列の型は{anchorName names}`String`、文字の型は{anchorName names}`Char`である。

:::paragraph
文字列は{anchorTerm helloWorld}`++`演算子で連結できる。
```anchor helloWorld
#eval "Hello, " ++ "world"
```
```anchorInfo helloWorld
"Hello, world"
```

文字列の末尾に文字を追加するには{anchorName pushExplicit}`String.push`を使う。
```anchor pushExplicit
#eval String.push "Hello" '!'
```
```anchorInfo pushExplicit
"Hello!"
```

この関数は、構造体のアクセサで使う{ref "behind-the-scenes"}[ドット記法]でも呼び出せる。
```anchor push
#eval "Hello".push '!'
```
```anchorInfo push
"Hello!"
```
:::


# スライス
%%%
tag := "string-slices"
%%%

文字列は、UTF-8エンコーディングによるバイト列と、キャッシュされた文字数の組として表される。
そのため、文字を一つ削るだけでも、残りの文字を新しい文字列にコピーすることになりうる。

文字列を扱うコードを、組み合わせやすい小さな部品から書けるようにするため、多くの文字列操作は{deftech}*文字列スライス*を返す。文字列スライスは、別の文字列の一部分を指すものである。
文字列スライスの型は{anchorName names}`String.Slice`である。
スライスは、ある文字列への参照と、スライスの開始位置と終了位置を保持する。複数のスライスが同じ文字列を共有できる。
文字列の先頭を落とすような操作は、新しい文字列を割り当てずにスライスを返す。文字列APIの大部分はスライス向けにも実装されている。

スライスを返す操作には、次のものがある。{anchorName names}`String.trimAscii`は、文字列の先頭と末尾から空白、タブ、改行、復帰の各文字を落としたスライスを返す。{anchorName names}`String.drop`と{anchorName names}`String.dropEnd`は、文字列の先頭または末尾から指定した数の文字を落とす。{anchorName names}`String.dropWhile`と{anchorName names}`String.dropEndWhile`は、それぞれパターンに一致する文字を先頭または末尾からすべて取り除く。
文字列の検索に使うパターンは、{ref "pattern-matching"}[パターンマッチング]のパターンとは別物である。文字列APIでは、一致させる文字や部分文字列を指定する関数の引数である。
文字列スライス向けのAPIにも、スライスを返す文字列関数が一通り用意されている。おかげで、途中で文字列をコピーしてしまう心配をせずに、文字列の操作を小さな手順の積み重ねとして書ける。

:::paragraph
次のコードは、途中で文字列を割り当てずに、文字列の先頭と末尾から文字を削る。
```anchor copy
#eval (("small tortoiseshell".drop 6).dropEnd 5).copy
```
```anchorInfo copy
"tortoise"
```
関数{anchorName names}`String.Slice.copy`は、スライスが指す範囲を元の文字列からコピーして返す。
最初の{anchorName names}`String.drop`の呼び出しはスライスを返し、{anchorName names}`String.Slice.dropEnd`の呼び出しは調整後のスライスを返す。
最後の{anchorName copy}`copy`の呼び出しで、再び文字列が作られる。
:::

文字列と違い、スライスは文字数をキャッシュしない。
文字のUTF-8エンコーディングが複数バイトになることがあるため、文字列スライスの長さを効率よく調べる方法はない。
ただし、空かどうかの判定は{anchorName names}`String.Slice.isEmpty`で行える。

# マッチング
%%%
tag := "string-matching"
%%%


{anchorName names}`String.dropWhile`や{anchorName names}`String.dropEndWhile`のように文字列の一部を照合する関数は、オーバーロードされている。
さまざまな*パターン*を渡して呼び出せ、それぞれが独自の方法で部分文字列に一致する。

:::paragraph
パターンには文字を指定できる。その場合は、その文字が連続している部分が取り除かれる。
```anchor dropEndWhileChar
#eval "red admiral".dropEndWhile 'l'
```
```anchorInfo dropEndWhileChar
red admira
```
文字列スライスなので、出力に引用符は付かない。文字列スライスは引用符なしで表示される。
パターンには文字列も指定でき、その場合はその文字列が連続している部分が取り除かれる。
```anchor dropWhileString
#eval "the the butterfly".dropWhile "the "
```
```anchorInfo dropWhileString
butterfly
```
一部分だけの一致は取り除かれない。
```anchor dropWhileString2
#eval ("a gray grayling".drop 2).dropWhile "gray "
```
```anchorInfo dropWhileString2
grayling
```
パターンには、{anchorName names}`true`か{anchorName names}`false`を返す関数も指定できる。
関数が{anchorName names}`false`を返すまで、文字が取り除かれる。
末尾の空白が残ることを示すために、スライスを文字列に変換している。
```anchor dropEndWhileFun
#eval ("red admiral".dropEndWhile Char.isAlpha).copy
```
```anchorInfo dropEndWhileFun
"red "
```
:::


# 出会うかもしれないメッセージ
%%%
tag := "string-messages-you-may-meet"
%%%

オーバーロードされた文字列照合の関数は、本書の後半で説明する機能、すなわち{ref "type-classes"}[型クラス]と{ref "dependent-types"}[依存型]を使って実装されている。
とくに、これらの機能を学ぶ前に読めるようになっておくと役立つエラーメッセージが二つある。

:::paragraph
パターンを渡さずにこれらの関数を呼ぶと、エラーになる。
```anchor dropEndWhileNoArg
#eval "red admiral".dropEndWhile
```
```anchorError dropEndWhileNoArg
don't know how to synthesize implicit argument `ρ`
  @String.dropEndWhile ?m.2 "red admiral"
context:
⊢ Type
```
このエラーは、パターンが与えられていないため、Leanがどのパターンの型を使えばよいか決められない、と言っている。
パターンを渡せば直る。
:::


:::paragraph
有効なパターンでない引数を渡して呼び出すと、コンパイル時のエラーになる。
```anchor dropEndWhileListArg
#eval "12345abcde".dropEndWhile [12]
```
```anchorError dropEndWhileListArg
failed to synthesize instance of type class
  String.Slice.Pattern.BackwardPattern [12]

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
このエラーメッセージは、パターン{anchorTerm dropEndWhileListArg}`[12]`に対して{anchorName names}`String.dropEndWhile`がオーバーロードされていない、という意味である。
関数、文字、文字列など、意味のあるパターンを渡せば直る。
:::
