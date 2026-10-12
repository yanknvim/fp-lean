module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.Arrays"

#doc (Manual) "Arrays and Termination" =>
%%%
tag := "array-termination"
%%%

効率のよいコードを書くには、適切なデータ構造を選ぶことが重要である。
連結リストにも役割がある。応用によっては、リストの残りを共有できることがとても重要である。
しかし、長さの変わる逐次的なデータの集まりの用途のほとんどには、メモリの負担が少なく局所性もよい配列のほうがよく合う。

しかし配列には、リストに対する二つの欠点がある。
 1. 配列はパターンマッチングではなく参照によって扱うので、安全性を保つために{ref "props-proofs-indexing"}[証明の義務]が課される。
 2. 配列全体を左から右へ処理するループは末尾再帰関数だが、呼び出しごとに小さくなる引数を持たない。

配列を有効に使うには、配列の添字が範囲内にあることをLeanに証明する方法と、配列の大きさに近づく添字がプログラムの停止ももたらすことを証明する方法を知る必要がある。
どちらも、命題としての等しさではなく、不等号の命題を使って表す。

# 不等号
%%%
tag := "inequality"
%%%

型によって順序の考え方が異なるので、不等号は{anchorName ordSugarClasses (module := Examples.Classes)}`LE`と{anchorName ordSugarClasses (module := Examples.Classes)}`LT`という二つの型クラスで扱う。
{ref "equality-and-ordering"}[標準の型クラス]の節の表が、これらのクラスと構文の関係を述べている。

:::table +header
*
  * 式
  * 脱糖した形
  * クラス名

*
  * {anchorTerm ltDesugar (module := Examples.Classes)}`x < y`
  * {anchorTerm ltDesugar (module := Examples.Classes)}`LT.lt x y`
  * {anchorName ordSugarClasses (module := Examples.Classes)}`LT`

*
  * {anchorTerm leDesugar (module := Examples.Classes)}`x ≤ y`
  * {anchorTerm leDesugar (module := Examples.Classes)}`LE.le x y`
  * {anchorName ordSugarClasses (module := Examples.Classes)}`LE`

*
  * {anchorTerm gtDesugar (module := Examples.Classes)}`x > y`
  * {anchorTerm gtDesugar (module := Examples.Classes)}`LT.lt y x`
  * {anchorName ordSugarClasses (module := Examples.Classes)}`LT`

*
  * {anchorTerm geDesugar (module := Examples.Classes)}`x ≥ y`
  * {anchorTerm geDesugar (module := Examples.Classes)}`LE.le y x`
  * {anchorName ordSugarClasses (module := Examples.Classes)}`LE`

:::

言い換えれば、型は{anchorTerm ltDesugar (module:=Examples.Classes)}`<`と{anchorTerm leDesugar (module:=Examples.Classes)}`≤`の意味を独自に定められ、{anchorTerm gtDesugar (module:=Examples.Classes)}`>`と{anchorTerm geDesugar (module:=Examples.Classes)}`≥`は{anchorTerm ltDesugar (module:=Examples.Classes)}`<`と{anchorTerm leDesugar (module:=Examples.Classes)}`≤`から意味を導く。
{anchorName ordSugarClasses (module := Examples.Classes)}`LT`と{anchorName ordSugarClasses (module := Examples.Classes)}`LE`クラスのメソッドは、{anchorName CoeBoolProp (module:=Examples.Classes)}`Bool`ではなく命題を返す。

```anchor less
class LE (α : Type u) where
  le : α → α → Prop

class LT (α : Type u) where
  lt : α → α → Prop
```

{anchorName LENat}`Nat`の{anchorName LENat}`LE`インスタンスは{anchorName LENat}`Nat.le`に委ねる。

```anchor LENat
instance : LE Nat where
  le := Nat.le
```
{anchorName LENat}`Nat.le`を定義するには、まだ紹介していないLeanの機能が要る。帰納的に定義された関係である。

## 帰納的に定義された命題・述語・関係
%%%
tag := "inductive-props"
%%%

{anchorName LENat}`Nat.le`は*帰納的に定義された関係*である。
{kw}`inductive`は新しいデータ型を作るのに使えるのと同じく、新しい命題を作るのにも使える。
命題が引数を取るとき、それを*述語*と呼び、起こりうる引数の一部については真になりうるが、すべてではない。
複数の引数を取る命題を*関係*と呼ぶ。

帰納的に定義された命題の各コンストラクタは、それを証明する一つの方法である。
言い換えれば、その命題の宣言は、それが真である証拠のさまざまな形を記述している。
引数がなくコンストラクタが一つの命題は、証明するのがとても簡単なことがある。

```anchor EasyToProve
inductive EasyToProve : Prop where
  | heresTheProof : EasyToProve
```
その証明は、そのコンストラクタを使うことから成る。

```anchor fairlyEasy
theorem fairlyEasy : EasyToProve := by
  constructor
```
実際、常に証明が簡単であるはずの命題{anchorName True}`True`も、{anchorName EasyToProve}`EasyToProve`とまったく同じように定義されている。

```anchor True
inductive True : Prop where
  | intro : True
```

引数を取らない帰納的に定義された命題は、帰納的に定義されたデータ型ほど面白くはない。
データはそれ自体が面白いからである。自然数{anchorTerm IsThree}`3`は数{lit}`35`とは異なり、ピザを3枚注文した人が30分後に35枚届いたら怒るだろう。
命題のコンストラクタは、その命題が真になりうる方法を記述するが、一度命題が証明されれば、*どの*コンストラクタが使われたかを知る必要はない。
{anchorTerm IsThree}`Prop`宇宙にある興味深い帰納的に定義された型のほとんどが引数を取るのはこのためである。

:::paragraph
帰納的に定義された述語{anchorName IsThree}`IsThree`は、その引数が3であることを述べている。

```anchor IsThree
inductive IsThree : Nat → Prop where
  | isThree : IsThree 3
```
ここで使う仕組みは{ref "column-pointers"}[{moduleName (module := Examples.DependentTypes.DB)}`HasCol`のような添字付き族]とまったく同じだが、得られる型が使えるデータではなく、証明できる命題である点が異なる。
:::

この述語を使うと、3が確かに3であることを証明できる。

```anchor threeIsThree
theorem three_is_three : IsThree 3 := by
  constructor
```
同様に、{anchorName IsFive}`IsFive`は、その引数が{anchorTerm IsFive}`5`であることを述べる述語である。

```anchor IsFive
inductive IsFive : Nat → Prop where
  | isFive : IsFive 5
```

ある数が3なら、それに2を足した結果は5になるはずである。
これは定理の言明として表せる。
```anchor threePlusTwoFive0
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  skip
```
得られるゴールは関数型を持つ。
```anchorError threePlusTwoFive0
unsolved goals
n : Nat
⊢ IsThree n → IsFive (n + 2)
```
したがって、{anchorTerm threePlusTwoFive1}`intro`タクティクを使ってその引数を前提に変換できる。
```anchor threePlusTwoFive1
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
```
```anchorError threePlusTwoFive1
unsolved goals
n : Nat
three : IsThree n
⊢ IsFive (n + 2)
```
{anchorName threePlusTwoFive1a}`n`が3であるという前提があれば、{anchorName threePlusTwoFive1a}`IsFive`のコンストラクタを使って証明を完成できるはずである。
```anchor threePlusTwoFive1a
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
  constructor
```
しかし、これはエラーになる。
```anchorError threePlusTwoFive1a
Tactic `constructor` failed: no applicable constructor found

n : Nat
three : IsThree n
⊢ IsFive (n + 2)
```
このエラーは、{anchorTerm threePlusTwoFive2}`n + 2`が{anchorTerm IsFive}`5`と定義上等しくないために起きる。
普通の関数定義では、前提{anchorName threePlusTwoFive2}`three`についての依存パターンマッチングを使い、{anchorName threePlusTwoFive2}`n`を{anchorTerm threeIsThree}`3`に洗練できる。
依存パターンマッチングに相当するタクティクは{anchorTerm threePlusTwoFive2}`cases`で、{kw}`induction`に似た構文を持つ。
```anchor threePlusTwoFive2
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
  cases three with
  | isThree => skip
```
残った場合では、{anchorName threePlusTwoFive2}`n`が{anchorTerm IsThree}`3`に洗練されている。
```anchorError threePlusTwoFive2
unsolved goals
case isThree
⊢ IsFive (3 + 2)
```
{anchorTerm various}`3 + 2`は{anchorTerm IsFive}`5`と定義上等しいので、コンストラクタが適用できるようになる。

```anchor threePlusTwoFive3
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
  cases three with
  | isThree => constructor
```

標準の偽の命題{anchorName various}`False`にはコンストラクタがなく、直接の証拠を与えることができない。
{anchorName various}`False`の証拠を与えられるのは、前提自体が不可能な場合だけであり、型システムが到達不可能と見抜けるコードに{kw}`nomatch`を使えるのと似ている。
{ref "connectives"}[証明についての最初の幕間]で述べたように、否定{anchorTerm various}`Not A`は{anchorTerm various}`A → False`の略である。
{anchorTerm various}`Not A`は{anchorTerm various}`¬A`とも書ける。

4が3であることはない。
```anchor fourNotThree0
theorem four_is_not_three : ¬ IsThree 4 := by
  skip
```
最初の証明のゴールには{anchorName fourNotThree1}`Not`が含まれる。
```anchorError fourNotThree0
unsolved goals
⊢ ¬IsThree 4
```
それが実際には関数型であることは{anchorTerm fourNotThree1}`unfold`で現せる。
```anchor fourNotThree1
theorem four_is_not_three : ¬ IsThree 4 := by
  unfold Not
```
```anchorError fourNotThree1
unsolved goals
⊢ IsThree 4 → False
```
ゴールが関数型なので、{anchorTerm fourNotThree2}`intro`を使ってその引数を前提に変換できる。
{anchorTerm fourNotThree2}`intro`が{anchorName fourNotThree1}`Not`の定義自体を展開できるので、{anchorTerm fourNotThree1}`unfold`は残す必要がない。
```anchor fourNotThree2
theorem four_is_not_three : ¬ IsThree 4 := by
  intro h
```
```anchorError fourNotThree2
unsolved goals
h : IsThree 4
⊢ False
```
この証明では、{anchorTerm fourNotThreeDone}`cases`タクティクがゴールをすぐに解決する。

```anchor fourNotThreeDone
theorem four_is_not_three : ¬ IsThree 4 := by
  intro h
  cases h
```
{anchorTerm otherEx (module:=Examples.DependentTypes)}`Vect String 2`についてのパターンマッチングに{anchorName otherEx (module:=Examples.DependentTypes)}`Vect.nil`の場合を含める必要がないのと同じく、{anchorTerm fourNotThreeDone}`IsThree 4`についての場合分けの証明には{anchorName IsThree}`isThree`の場合を含める必要がない。

## 自然数の不等号
%%%
tag := "inequality-of-natural-numbers"
%%%

{anchorName NatLe}`Nat.le`の定義にはパラメータと添字がある。

```anchor NatLe
inductive Nat.le (n : Nat) : Nat → Prop
  | refl : Nat.le n n
  | step : Nat.le n m → Nat.le n (m + 1)
```
パラメータ{anchorName NatLe}`n`は小さいほうの数であり、添字は{anchorName NatLe}`n`以上であるべき数である。
{anchorName NatLe}`refl`コンストラクタは両方の数が等しいときに使い、{anchorName NatLe}`step`コンストラクタは添字が{anchorName NatLe}`n`より大きいときに使う。

証拠の観点では、$`n \leq k`の証明は、$`n + d = m`となるようなある数$`d`を見つけることから成る。
Leanでは、その証明は{anchorName leNames}`Nat.le.refl`コンストラクタを$`d`個の{anchorName leNames}`Nat.le.step`で包んだものになる。
各{anchorName NatLe}`step`コンストラクタはその添字の引数に1を加えるので、$`d`個の{anchorName NatLe}`step`コンストラクタは大きいほうの数に$`d`を加える。
たとえば、4が7以下である証拠は、{anchorName NatLe}`refl`を3個の{anchorName NatLe}`step`で包んだものである。

```anchor four_le_seven
theorem four_le_seven : 4 ≤ 7 :=
  open Nat.le in
  step (step (step refl))
```

狭義の小なり関係は、左側の数に1を加えることで定義する。

```anchor NatLt
def Nat.lt (n m : Nat) : Prop :=
  Nat.le (n + 1) m

instance : LT Nat where
  lt := Nat.lt
```
4が7より真に小さい証拠は、{anchorName four_lt_seven}`refl`を2個の{anchorName four_lt_seven}`step`で包んだものである。

```anchor four_lt_seven
theorem four_lt_seven : 4 < 7 :=
  open Nat.le in
  step (step refl)
```
{anchorTerm four_lt_seven}`4 < 7`が{anchorTerm four_lt_seven_alt}`5 ≤ 7`と等価だからである。

# 停止性の証明
%%%
tag := "proving-termination"
%%%

{anchorName ArrayMap}`Array.map`関数は、配列を関数で変換し、入力の配列の各要素に関数を適用した結果を含む新しい配列を返す。
これを末尾再帰関数として書くには、出力の配列をアキュムレータとして渡す関数に委ねるという、いつもの形に従う。
アキュムレータは空の配列で初期化する。
アキュムレータを渡す補助関数は、配列の現在の添字を追跡する引数も取り、それは{anchorTerm ArrayMap}`0`から始まる。

```anchor ArrayMap
def Array.map (f : α → β) (arr : Array α) : Array β :=
  arrayMapHelper f arr Array.empty 0
```

補助関数は、繰り返しごとに、添字がまだ範囲内かを調べるべきである。
範囲内なら、変換した要素をアキュムレータの末尾に加え、添字を{anchorTerm mapHelperIndexIssue}`1`増やして再びループすべきである。
そうでなければ、終了してアキュムレータを返すべきである。
このコードの最初の実装は、Leanが配列の添字が妥当であることを証明できないため失敗する。
```anchor mapHelperIndexIssue
def arrayMapHelper (f : α → β) (arr : Array α)
    (soFar : Array β) (i : Nat) : Array β :=
  if i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else soFar
```
```anchorError mapHelperIndexIssue
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.1811
β : Type ?u.1814
f : α → β
arr : Array α
soFar : Array β
i : Nat
⊢ i < arr.size
```
しかし、この条件式は、配列の添字の妥当性が要求するまさにその条件（つまり{anchorTerm arrayMapHelperTermIssue}`i < arr.size`）をすでに調べている。
{kw}`if`に名前を付けると問題が解決する。配列の参照のタクティクが使える前提が加わるためである。

```anchor arrayMapHelperTermIssue
def arrayMapHelper (f : α → β) (arr : Array α)
    (soFar : Array β) (i : Nat) : Array β :=
  if inBounds : i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else soFar
```
再帰呼び出しが入力のコンストラクタの引数に対して行われていないにもかかわらず、Leanは修正したプログラムを受け付ける。
実際、アキュムレータも添字も、小さくなるどころか大きくなる。

裏では、Leanの証明の自動化が停止性の証明を組み立てる。
この証明を再構成すると、Leanが自動で見抜けない場合を理解しやすくなる。

{anchorName arrayMapHelperTermIssue}`arrayMapHelper`はなぜ停止するのか。
各繰り返しで、添字{anchorName arrayMapHelperTermIssue}`i`が配列{anchorName arrayMapHelperTermIssue}`arr`でまだ範囲内かを調べる。
範囲内なら、{anchorName arrayMapHelperTermIssue}`i`が増やされてループが繰り返される。
そうでなければ、プログラムは終了する。
{anchorTerm arrayMapHelperTermIssue}`arr.size`は有限の数なので、{anchorName arrayMapHelperTermIssue}`i`を増やせる回数は有限である。
関数のどの引数も呼び出しごとに小さくならないが、{anchorTerm ArrayMapHelperOk}`arr.size - i`は0に向かって小さくなる。

再帰呼び出しごとに小さくなる値を*尺度*と呼ぶ。
定義の末尾に{kw}`termination_by`の句を書くと、停止性の尺度として特定の式を使うようLeanに指示できる。
{anchorName ArrayMapHelperOk}`arrayMapHelper`では、明示的な尺度は次のようになる。

```anchor ArrayMapHelperOk
def arrayMapHelper (f : α → β) (arr : Array α)
    (soFar : Array β) (i : Nat) : Array β :=
  if inBounds : i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else soFar
termination_by arr.size - i
```

同様の停止性の証明を使って{anchorName ArrayFind}`Array.find`を書ける。これは配列の中で真偽値の関数を満たす最初の要素を見つけ、その要素と添字の両方を返す関数である。

```anchor ArrayFind
def Array.find (arr : Array α) (p : α → Bool) :
    Option (Nat × α) :=
  findHelper arr p 0
```
ここでもまた、{lit}`i`が増えるにつれ{lit}`arr.size - i`が小さくなるので、補助関数は停止する。

```anchor ArrayFindHelper
def findHelper (arr : Array α) (p : α → Bool)
    (i : Nat) : Option (Nat × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (i, x)
    else findHelper arr p (i + 1)
  else none
```

{kw}`termination_by`に疑問符を付ける（つまり{kw}`termination_by?`を使う）と、Leanが自分で選んだ尺度を明示的に提案する。
{lit}`[apply]`をクリックすると、{kw}`termination_by?`が提案された尺度で置き換わる。
```anchor ArrayFindHelperSugg
def findHelper (arr : Array α) (p : α → Bool)
    (i : Nat) : Option (Nat × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (i, x)
    else findHelper arr p (i + 1)
  else none
termination_by?
```
```anchorInfo ArrayFindHelperSugg
Try this:
  [apply] termination_by arr.size - i
```

停止性の議論がすべてこれほど単純なわけではない。
しかし、関数の引数に基づいて呼び出しごとに小さくなる何らかの式を見つけるという基本的な構造は、すべての停止性の証明に現れる。
関数がなぜ停止するのかを突き止めるのに工夫が要ることもあり、その尺度が実際に小さくなることをLeanに受け入れさせるのに追加の証明が要ることもある。



# 練習問題
%%%
tag := "array-termination-exercises"
%%%

 * 末尾再帰でアキュムレータを渡す関数と{kw}`termination_by`の句を使って、配列に対する{anchorTerm ForMArr}`ForM m (Array α)`インスタンスを実装せよ。
 * {anchorName ArrayMap}`Array.map`、{anchorName ArrayFind}`Array.find`、{anchorName ForMArr}`ForM`インスタンスを、恒等モナドでの{kw}`for`{lit}` ... `{kw}`in`{lit}` ...`ループを使って実装し直し、得られるコードを比べよ。
 * 配列の反転を、恒等モナドでの{kw}`for`{lit}` ... `{kw}`in`{lit}` ...`ループを使って実装し直せ。末尾再帰関数と比べよ。
