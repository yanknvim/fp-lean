module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.Fin"

#doc (Manual) "Bounded Numbers" =>
%%%
tag := "Fin"
%%%

{anchorName sundries}`Array`と{anchorName sundries}`Nat`の{anchorTerm sundries}`GetElem`インスタンスは、与えられた{anchorName sundries}`Nat`が配列より小さいという証明を要求する。
実際には、これらの証明はしばしば添字とともに特に関数へ渡されることになる。
添字と証明を別々に渡す代わりに、{anchorName Fin}`Fin`という型を使って添字と証明を一つの値にまとめられる。
これでコードが読みやすくなることがある。

型{anchorTerm sundries}`Fin n`は{anchorName sundries}`n`より真に小さい数を表す。
言い換えれば、{anchorTerm sundries}`Fin 3`は{anchorTerm sundries}`0`、{anchorTerm sundries}`1`、{anchorTerm sundries}`2`を記述し、{anchorTerm sundries}`Fin 0`には値がまったくない。
{anchorName Fin}`Fin`の定義は{anchorName sundries}`Subtype`に似ており、{anchorTerm sundries}`Fin n`は{anchorName Fin}`Nat`と、それが{anchorName sundries}`n`より小さいという証明を含む構造体である。

```anchor Fin
structure Fin (n : Nat) where
  val  : Nat
  isLt : LT.lt val n
```

Leanには{anchorName sundries}`ToString`と{anchorName sundries}`OfNat`のインスタンスがあり、{anchorName Fin}`Fin`の値を数として便利に使える。
言い換えれば、{anchorTerm fiveFinEight}`#eval (5 : Fin 8)`の出力は{lit}`{val := 5, isLt := _}`のようなものではなく{anchorInfo fiveFinEight}`5`である。

与えられた数が上限より大きいときに失敗する代わりに、{anchorName Fin}`Fin`の{anchorName sundries}`OfNat`インスタンスは上限を法とした値を返す。
つまり、{anchorTerm finOverflow}`#eval (45 : Fin 10)`はコンパイル時のエラーではなく{anchorInfo finOverflow}`5`になる。

戻り値の型で、見つかった添字として{anchorName Fin}`Fin`を返すと、それが見つかったデータ構造との結び付きがより明確になる。
{ref "proving-termination"}[前の節]の{anchorName ArrayFind}`Array.find`は、呼び出し側がすぐには配列の参照に使えない添字を返す。その妥当性についての情報が失われているためである。
より具体的な型にすると、プログラムをそれほど複雑にせずに使える値が得られる。

```anchor ArrayFindHelper
def findHelper (arr : Array α) (p : α → Bool) (i : Nat) :
    Option (Fin arr.size × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (⟨i, h⟩, x)
    else findHelper arr p (i + 1)
  else none
```

```anchor ArrayFind
def Array.find (arr : Array α) (p : α → Bool) : Option (Fin arr.size × α) :=
  findHelper arr p 0
```

# 練習問題
%%%
tag := "Fin-exercises"
%%%

範囲内ならその次に大きい{anchorName nextThreeFin}`Fin`を返し、そうでなければ{anchorName ArrayFindHelper}`none`を返す{anchorTerm exercise}`Fin.next? : Fin n → Option (Fin n)`関数を書け。
まず、次を実行すると、
```anchor nextThreeFin
#eval (3 : Fin 8).next?
```
次の出力になることを確かめよ。
```anchorInfo nextThreeFin
some 4
```
また、
```anchor nextSevenFin
#eval (7 : Fin 8).next?
```
次の出力になることを確かめよ。
```anchorInfo nextSevenFin
none
```
