module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.Inequalities"

#doc (Manual) "More Inequalities" =>
%%%
tag := "more-inequalities"
%%%

Leanに組み込みの証明の自動化は、{anchorName ArrayMapHelperOk (module:=Examples.ProgramsProofs.Arrays)}`arrayMapHelper`と{anchorName ArrayFindHelper (module:=Examples.ProgramsProofs.Arrays)}`findHelper`が停止することを調べるのに十分であった。
必要だったのは、再帰呼び出しごとに値が小さくなる式を与えることだけだった。
しかし、Leanに組み込みの自動化は魔法ではなく、しばしば助けが要る。

# マージソート
%%%
tag := "merge-sort"
%%%


停止性の証明が自明でない関数の例が、{moduleName}`List`のマージソートである。
マージソートは二つの段階から成る。まず、リストを半分に分ける。
それぞれの半分をマージソートで並べ替え、次に、二つの整列済みのリストをより大きな整列済みのリストにまとめる関数でその結果を併合する。
基底の場合は空のリストと単一要素のリストであり、どちらもすでに整列済みと見なす。

二つの整列済みのリストを併合するには、基本的な場合を二つ考える。
 1. 入力のリストの一方が空なら、結果は他方のリストである。
 2. どちらのリストも空でなければ、それらの先頭を比べる。この関数の結果は、二つの先頭のうち小さいほうの後に、両方のリストの残りの要素を併合した結果を続けたものである。

これはどちらのリストについても構造的再帰ではない。
再帰が停止するのは、再帰呼び出しごとに二つのリストの一方から要素が取り除かれるためだが、どちらのリストからでもありうる。
裏では、Leanがこの事実を使って停止することを証明する。

```anchor merge
def merge [Ord α] (xs : List α) (ys : List α) : List α :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x'::xs', y'::ys' =>
    match Ord.compare x' y' with
    | .lt | .eq => x' :: merge xs' (y' :: ys')
    | .gt => y' :: merge (x'::xs') ys'
```


リストを分ける単純な方法は、入力のリストの各要素を二つの出力リストに交互に加えることである。

```anchor splitList
def splitList (lst : List α) : (List α × List α) :=
  match lst with
  | [] => ([], [])
  | x :: xs =>
    let (a, b) := splitList xs
    (x :: b, a)
```
この分割の関数は構造的再帰である。

マージソートは基底の場合に達したかを調べる。
達していれば、入力のリストを返す。
達していなければ、入力を分け、それぞれの半分を並べ替えた結果を併合する。
```anchor mergeSortNoTerm
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    merge (mergeSort halves.fst) (mergeSort halves.snd)
```
Leanのパターンマッチのコンパイラは、{anchorTerm mergeSortNoTerm}`xs.length < 2`を調べる{kw}`if`が導入する前提{anchorName mergeSortNoTerm}`h`が、要素が一つより多いリストを排除していると判断できるので、「場合の欠落」のエラーは出ない。
しかし、このプログラムは常に停止するが構造的再帰ではなく、Leanは小さくなる尺度を自動で見つけられない。
```anchorError mergeSortNoTerm
fail to show termination for
  mergeSort
with errors
failed to infer structural recursion:
Not considering parameter α of mergeSort:
  it is unchanged in the recursive calls
Not considering parameter #2 of mergeSort:
  it is unchanged in the recursive calls
Cannot use parameter xs:
  failed to eliminate recursive application
    mergeSort halves.fst


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
            xs #1
1) 70:11-31  ?  ?
2) 70:34-54  _  _

#1: xs.length

Please use `termination_by` to specify a decreasing measure.
```
停止するのは、少なくとも二つ以上の要素を含むリストに適用したときは、{anchorName mergeSortNoTerm}`splitList`が常に入力より短いリストを返すためである。
つまり、{anchorTerm mergeSortNoTerm}`halves.fst`と{anchorTerm mergeSortNoTerm}`halves.snd`の長さは{anchorName mergeSortNoTerm}`xs`の長さより小さい。
これは{kw}`termination_by`の句で表せる。
```anchor mergeSortGottaProveIt
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length
```
この句を書くと、エラーメッセージが変わる。
関数が構造的再帰でないと文句を言う代わりに、Leanは{lit}`(splitList xs).fst.length < xs.length`を自動で証明できなかったと指摘する。
```anchorError mergeSortGottaProveIt
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
α : Type u_1
xs : List α
h : ¬xs.length < 2
halves : List α × List α := splitList xs
⊢ (splitList xs).fst.length < xs.length
```

# リストを分けると短くなる
%%%
tag := "splitting-shortens"
%%%

{lit}`(splitList xs).snd.length < xs.length`も証明する必要がある。
{anchorName splitList}`splitList`は二つのリストに交互に要素を加えるので、両方の言明を一度に証明するのが最も簡単であり、証明の構造を{anchorName splitList}`splitList`の実装の算法に合わせられる。
言い換えれば、{anchorTerm splitList_shorter_bad_ty}`∀(lst : List α), (splitList lst).fst.length < lst.length ∧ (splitList lst).snd.length < lst.length`を証明するのが最も簡単である。

残念ながら、この言明は偽である。
特に、{anchorTerm splitListEmpty}`splitList []`は{anchorTerm splitListEmpty}`([], [])`である。どちらの出力リストの長さも{anchorTerm ArrayMap (module:=Examples.ProgramsProofs.Arrays)}`0`であり、入力のリストの長さである{anchorTerm ArrayMap (module:=Examples.ProgramsProofs.Arrays)}`0`より小さくない。
同様に、{anchorTerm splitListOne}`splitList ["basalt"]`は{anchorTerm splitListOne}`(["basalt"], [])`に評価され、{anchorTerm splitListOne}`["basalt"]`は{anchorTerm splitListOne}`["basalt"]`より短くない。
しかし、{anchorTerm splitListTwo}`splitList ["basalt", "granite"]`は{anchorTerm splitListTwo}`(["basalt"], ["granite"])`に評価され、どちらの出力リストも入力のリストより短い。

出力リストの長さは常に入力のリストの長さ以下であり、入力のリストが少なくとも二つの要素を含むときにだけ真に短くなることが分かる。
前者の言明を証明し、それを後者の言明に拡張するのが最も簡単であることが分かる。
まず定理の言明を書く。
```anchor splitList_shorter_le0
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  skip
```
```anchorError splitList_shorter_le0
unsolved goals
α : Type u_1
lst : List α
⊢ (splitList lst).fst.length ≤ lst.length ∧ (splitList lst).snd.length ≤ lst.length
```
{anchorName splitList}`splitList`はリストについて構造的再帰なので、証明には帰納法を使うべきである。
{anchorName splitList}`splitList`の構造的再帰は帰納法による証明にぴったり合う。帰納法の基底の場合は再帰の基底の場合に一致し、帰納法の段階は再帰呼び出しに一致する。
{kw}`induction`タクティクは二つのゴールを与える。
```anchor splitList_shorter_le1a
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => skip
  | cons x xs ih => skip
```
```anchorError splitList_shorter_le1a
unsolved goals
case nil
α : Type u_1
⊢ (splitList []).fst.length ≤ [].length ∧ (splitList []).snd.length ≤ [].length
```
```anchorError splitList_shorter_le1b
unsolved goals
case cons
α : Type u_1
x : α
xs : List α
ih : (splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length
⊢ (splitList (x :: xs)).fst.length ≤ (x :: xs).length ∧ (splitList (x :: xs)).snd.length ≤ (x :: xs).length
```

{anchorName splitList_shorter_le2}`nil`の場合のゴールは、単純化器を呼び出し、{anchorName splitList}`splitList`の定義を展開するよう指示すれば証明できる。空のリストの長さは空のリストの長さ以下だからである。
同様に、{anchorName splitList_shorter_le2}`cons`の場合に{anchorName splitList}`splitList`で単純化すると、ゴールの長さの周りに{anchorName various}`Nat.succ`が付く。
```anchor splitList_shorter_le2
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => simp [splitList]
  | cons x xs ih =>
    simp [splitList]
```
```anchorError splitList_shorter_le2
unsolved goals
case cons
α : Type u_1
x : α
xs : List α
ih : (splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length
⊢ (splitList xs).snd.length ≤ xs.length ∧ (splitList xs).fst.length ≤ xs.length + 1
```
これは、{anchorName various}`List.length`の呼び出しがリスト{anchorTerm splitList}`x :: xs`の先頭を消費し、入力のリストの長さと最初の出力リストの長さの両方でそれを{anchorName various}`Nat.succ`に変えるためである。

Leanで{anchorTerm various}`A ∧ B`と書くのは{anchorTerm various}`And A B`の略である。
{anchorName And}`And`は{anchorTerm And}`Prop`宇宙の構造体型である。

```anchor And
structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b
```
言い換えれば、{anchorTerm various}`A ∧ B`の証明は、{anchorName AndUse}`And.intro`コンストラクタを、{anchorName And}`left`フィールドに{anchorName AndUse}`A`の証明、{anchorName And}`right`フィールドに{anchorName AndUse}`B`の証明とともに適用したものである。

{kw}`cases`タクティクを使うと、証明でデータ型の各コンストラクタ、または命題の起こりうる各証明を順に考えることができる。
これは再帰のない{kw}`match`式に相当する。
構造体に{kw}`cases`を使うと、その構造体が分解され、その構造体の各フィールドに対して前提が加わる。パターンマッチの式がプログラムで使うために構造体のフィールドを取り出すのと同じである。
構造体にはコンストラクタが一つしかないので、構造体に{kw}`cases`を使ってもゴールは増えない。

{anchorName splitList_shorter_le3}`ih`は{lit}`List.length (splitList xs).fst ≤ List.length xs ∧ List.length (splitList xs).snd ≤ List.length xs`の証明なので、{anchorTerm splitList_shorter_le3}`cases ih`を使うと、{lit}`List.length (splitList xs).fst ≤ List.length xs`という前提と、{lit}`List.length (splitList xs).snd ≤ List.length xs`という前提が得られる。
```anchor splitList_shorter_le3
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => simp [splitList]
  | cons x xs ih =>
    simp [splitList]
    cases ih
```
```anchorError splitList_shorter_le3
unsolved goals
case cons.intro
α : Type u_1
x : α
xs : List α
left✝ : (splitList xs).fst.length ≤ xs.length
right✝ : (splitList xs).snd.length ≤ xs.length
⊢ (splitList xs).snd.length ≤ xs.length ∧ (splitList xs).fst.length ≤ xs.length + 1
```

証明のゴールも{anchorName AndUse}`And`なので、{kw}`constructor`タクティクで{anchorName AndUse}`And.intro`を適用でき、各引数についてのゴールになる。
```anchor splitList_shorter_le4
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => simp [splitList]
  | cons x xs ih =>
    simp [splitList]
    cases ih
    constructor
```
```anchorError splitList_shorter_le4
unsolved goals
case cons.intro.left
α : Type u_1
x : α
xs : List α
left✝ : (splitList xs).fst.length ≤ xs.length
right✝ : (splitList xs).snd.length ≤ xs.length
⊢ (splitList xs).snd.length ≤ xs.length

case cons.intro.right
α : Type u_1
x : α
xs : List α
left✝ : (splitList xs).fst.length ≤ xs.length
right✝ : (splitList xs).snd.length ≤ xs.length
⊢ (splitList xs).fst.length ≤ xs.length + 1
```

{anchorTerm splitList_shorter_le5}`left`のゴールは{lit}`left✝`の前提と同一なので、{kw}`assumption`タクティクで片付けられる。
```anchor splitList_shorter_le5
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => simp [splitList]
  | cons x xs ih =>
    simp [splitList]
    cases ih
    constructor
    case left => assumption
```
```anchorError splitList_shorter_le5
unsolved goals
case cons.intro.right
α : Type u_1
x : α
xs : List α
left✝ : (splitList xs).fst.length ≤ xs.length
right✝ : (splitList xs).snd.length ≤ xs.length
⊢ (splitList xs).fst.length ≤ xs.length + 1
```


{anchorTerm splitList_shorter_le}`right`のゴールは{lit}`right✝`の前提に似ているが、ゴールでは入力のリストの長さにだけ{anchorTerm le_succ_of_le}`+ 1`が加わっている。
この不等式が成り立つことを証明する時である。

## 大きいほうの辺に1を加える
%%%
tag := "le-succ-of-le"
%%%

{anchorName splitList_shorter_le}`splitList_shorter_le`を証明するのに必要な不等式は{anchorTerm le_succ_of_le_statement}`∀(n m : Nat), n ≤ m → n ≤ m + 1`である。
入ってくる{anchorTerm le_succ_of_le_statement}`n ≤ m`という前提は、本質的に{anchorName le_succ_of_le_statement}`n`と{anchorName le_succ_of_le_statement}`m`の差を{anchorName le_succ_of_le_apply}`Nat.le.step`コンストラクタの数として追跡している。
したがって、証明は基底の場合に{anchorName le_succ_of_le_apply}`Nat.le.step`を一つ余分に加えるべきである。

まず、言明は次のようになる。
```anchor le_succ_of_le0
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  skip
```
```anchorError le_succ_of_le0
unsolved goals
n m : Nat
⊢ n ≤ m → n ≤ m + 1
```

まず、{anchorTerm le_succ_of_le1}`n ≤ m`という前提に名前を導入する。
```anchor le_succ_of_le1
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
```
```anchorError le_succ_of_le1
unsolved goals
n m : Nat
h : n ≤ m
⊢ n ≤ m + 1
```

証明はこの前提についての帰納法による。
```anchor le_succ_of_le2a
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => skip
  | step _ ih => skip
```
{anchorName le_succ_of_le2a}`refl`の場合（{lit}`n = m`）では、{lit}`n ≤ n + 1`を証明することがゴールである。
```anchorError le_succ_of_le2a
unsolved goals
case refl
n m : Nat
⊢ n ≤ n + 1
```
{anchorName le_succ_of_le2b}`step`の場合は、{anchorTerm le_succ_of_le2b}`n ≤ m`という前提の下で{anchorTerm le_succ_of_le2b}`n ≤ m + 1`を証明することがゴールである。
```anchorError le_succ_of_le2b
unsolved goals
case step
n m m✝ : Nat
a✝ : n.le m✝
ih : n ≤ m✝ + 1
⊢ n ≤ m✝.succ + 1
```

{anchorName le_succ_of_le3}`refl`の場合は、{anchorName le_succ_of_le3}`step`コンストラクタを適用できる。
```anchor le_succ_of_le3
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => constructor
  | step _ ih => skip
```
```anchorError le_succ_of_le3
unsolved goals
case refl
n m : Nat
⊢ n.le n
```
{anchorName Nat.le_ctors}`step`の後に{anchorName Nat.le_ctors}`refl`を使え、{anchorName le_succ_of_le4}`step`のゴールだけが残る。
```anchor le_succ_of_le4
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => constructor; constructor
  | step _ ih => skip
```
```anchorError le_succ_of_le4
unsolved goals
case step
n m m✝ : Nat
a✝ : n.le m✝
ih : n ≤ m✝ + 1
⊢ n ≤ m✝.succ + 1
```

段階の場合は、{anchorName Nat.le_ctors}`step`コンストラクタを適用するとゴールが帰納法の仮定に変わる。
```anchor le_succ_of_le5
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => constructor; constructor
  | step _ ih => constructor
```
```anchorError le_succ_of_le5
unsolved goals
case step
n m m✝ : Nat
a✝ : n.le m✝
ih : n ≤ m✝ + 1
⊢ n.le (m✝ + 1)
```

最終的な証明は次のとおりである。

```anchor le_succ_of_le
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => constructor; constructor
  | step => constructor; assumption
```

裏で何が起きているかを明らかにするには、{kw}`apply`と{kw}`exact`タクティクを使い、どのコンストラクタが適用されているかを正確に示せる。
{kw}`apply`タクティクは、戻り値の型が一致する関数やコンストラクタを適用して現在のゴールを解き、与えられなかった引数ごとに新しいゴールを作る。一方{kw}`exact`は、新しいゴールが必要になるなら失敗する。

```anchor le_succ_of_le_apply
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => apply Nat.le.step; exact Nat.le.refl
  | step _ ih => apply Nat.le.step; exact ih
```

証明はゴルフできる。

```anchor le_succ_of_le_golf
theorem Nat.le_succ_of_le (h : n ≤ m) : n ≤ m + 1:= by
  induction h <;> repeat (first | constructor | assumption)
```
この短いタクティクの筋書きでは、{kw}`induction`が導入した両方のゴールが{anchorTerm le_succ_of_le_golf}`repeat (first | constructor | assumption)`で扱われる。
{lit}`first | T1 | T2 | ... | Tn`というタクティクは、{lit}`T1`から{lit}`Tn`まで順に試し、最初に成功したタクティクを使うことを意味する。
言い換えれば、{anchorTerm le_succ_of_le_golf}`repeat (first | constructor | assumption)`はコンストラクタを適用できるだけ適用し、次に前提を使ってゴールを解こうとする。

{tactic}`grind`を使えば証明をさらに短くできる。これには線形算術の解決器が含まれている。

```anchor le_succ_of_le_grind
theorem Nat.le_succ_of_le (h : n ≤ m) : n ≤ m + 1:= by
  grind
```

最後に、証明は再帰関数として書ける。

```anchor le_succ_of_le_recursive
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1
  | .refl => .step .refl
  | .step h => .step (Nat.le_succ_of_le h)
```

それぞれの証明の流儀は、違う状況に適している。
詳しい証明の筋書きは、初心者がコードを読むかもしれない場合や、証明の各段階が何らかの洞察を与える場合に役に立つ。
短く高度に自動化された証明の筋書きは、通常は保守しやすい。自動化はしばしば、定義やデータ型への小さな変更に対して柔軟で頑健だからである。
再帰関数は通常、数学的な証明の観点からは理解しにくく保守も難しいが、対話的な定理証明を始めたプログラマにとって役に立つ橋渡しになりうる。

## 証明の仕上げ
%%%
tag := "finishing-splitList-shorter-proof"
%%%

両方の補助定理を証明したので、{anchorName splitList_shorter_le5}`splitList_shorter_le`の残りはすぐに完成する。
現在の証明の状態にはゴールが一つ残っている。
```anchorError splitList_shorter_le5
unsolved goals
case cons.intro.right
α : Type u_1
x : α
xs : List α
left✝ : (splitList xs).fst.length ≤ xs.length
right✝ : (splitList xs).snd.length ≤ xs.length
⊢ (splitList xs).fst.length ≤ xs.length + 1
```

{anchorName splitList_shorter_le}`Nat.le_succ_of_le`を{lit}`right✝`の前提とともに使うと証明が完成する。

```anchor splitList_shorter_le
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => simp [splitList]
  | cons x xs ih =>
    simp [splitList]
    cases ih
    constructor
    case left => assumption
    case right =>
      apply Nat.le_succ_of_le
      assumption
```

次は、マージソートが停止することを証明するのに必要な本来の定理に戻る。リストが少なくとも二つの要素を持つ限り、それを分けた結果のどちらも真に短い、というものである。
```anchor splitList_shorter_start
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := by
  skip
```
```anchorError splitList_shorter_start
unsolved goals
α : Type u_1
lst : List α
x✝ : lst.length ≥ 2
⊢ (splitList lst).fst.length < lst.length ∧ (splitList lst).snd.length < lst.length
```
パターンマッチングは、プログラムと同様にタクティクの筋書きでも問題なく働く。
{anchorName splitList_shorter_1}`lst`は少なくとも二つの要素を持つので、{kw}`match`でそれらを現せる。これも依存パターンマッチングによって型を洗練する。
```anchor splitList_shorter_1
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := by
  match lst with
  | x :: y :: xs =>
    skip
```
```anchorError splitList_shorter_1
unsolved goals
α : Type u_1
lst : List α
x y : α
xs : List α
x✝ : (x :: y :: xs).length ≥ 2
⊢ (splitList (x :: y :: xs)).fst.length < (x :: y :: xs).length ∧
  (splitList (x :: y :: xs)).snd.length < (x :: y :: xs).length
```
{anchorName splitList}`splitList`を使って単純化すると{anchorName splitList_shorter_2}`x`と{anchorName splitList_shorter_2}`y`が取り除かれ、計算されたリストの長さにそれぞれ{anchorTerm le_succ_of_le}`+ 1`が付く。
```anchor splitList_shorter_2
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := by
  match lst with
  | x :: y :: xs =>
    simp [splitList]
```
```anchorError splitList_shorter_2
unsolved goals
α : Type u_1
lst : List α
x y : α
xs : List α
x✝ : (x :: y :: xs).length ≥ 2
⊢ (splitList xs).fst.length < xs.length + 1 ∧ (splitList xs).snd.length < xs.length + 1
```
{anchorTerm splitList_shorter_2b}`simp`を{anchorTerm splitList_shorter_2b}`simp +arith`に置き換えると、これらの{anchorTerm le_succ_of_le}`+ 1`が取り除かれる。{anchorTerm splitList_shorter_2b}`simp +arith`が、{anchorTerm Nat.lt_imp}`n + 1 < m + 1`ならば{anchorTerm Nat.lt_imp}`n < m`であるという事実を使うためである。
```anchor splitList_shorter_2b
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := by
  match lst with
  | x :: y :: xs =>
    simp +arith [splitList]
```
```anchorError splitList_shorter_2b
unsolved goals
α : Type u_1
lst : List α
x y : α
xs : List α
x✝ : (x :: y :: xs).length ≥ 2
⊢ (splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length
```
このゴールは{anchorName splitList_shorter}`splitList_shorter_le`に一致し、これを使って証明を締めくくれる。

```anchor splitList_shorter
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := by
  match lst with
  | x :: y :: xs =>
    simp +arith [splitList]
    apply splitList_shorter_le
```

{anchorName mergeSort}`mergeSort`が停止することを証明するのに必要な事実は、得られた{anchorName AndUse}`And`から取り出せる。

```anchor splitList_shorter_sides
theorem splitList_shorter_fst (lst : List α) (h : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length :=
  splitList_shorter lst h |>.left

theorem splitList_shorter_snd (lst : List α) (h : lst.length ≥ 2) :
    (splitList lst).snd.length < lst.length :=
  splitList_shorter lst h |>.right
```

## より簡単な証明
%%%
tag := "splitList-shorter-le-simpler-proof"
%%%


:::paragraph
普通の帰納法を使う代わりに、{anchorName splitList_shorter_le_funInd1}`splitList_shorter_le`は関数による帰納法で証明でき、{anchorName splitList}`splitList`の枝ごとに一つの場合が得られる。
```anchor splitList_shorter_le_funInd1
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  fun_induction splitList with
  | case1 => skip
  | case2 x xs a b splitEq ih => skip
```
一つ目の場合は{anchorName splitList}`splitList`の基底の場合に一致する。
{anchorName splitList}`splitList`の*両方*の適用が、この最初の枝の結果で置き換えられている。
```anchorError splitList_shorter_le_funInd1
unsolved goals
case case1
α : Type u_1
⊢ ([], []).fst.length ≤ [].length ∧ ([], []).snd.length ≤ [].length
```
二つ目の場合は{anchorName splitList}`splitList`の再帰の枝に一致する。
帰納法の仮定に加えて、{anchorName splitList}`splitList`の{anchorTerm splitList}`let`の値が前提で追跡されている。
```anchorError splitList_shorter_le_funInd1
unsolved goals
case case2
α : Type u_1
x : α
xs a b : List α
splitEq : splitList xs = (a, b)
ih : (splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length
⊢ (x :: b, a).fst.length ≤ (x :: xs).length ∧ (x :: b, a).snd.length ≤ (x :: xs).length
```
:::

二つ目の場合は少し複雑に見えるが、証明を完成させるのに必要なものはすべてそろっている。
実際、{tactic}`grind`が両方のゴールをすぐに証明できる。
```anchor splitList_shorter_le_funInd2
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  fun_induction splitList <;> grind
```

# マージソートの停止
%%%
tag := "merge-sort-terminates"
%%%

マージソートには再帰呼び出しが二つあり、{anchorName splitList}`splitList`が返す部分リストごとに一つずつである。
各再帰呼び出しには、渡されるリストの長さが入力のリストの長さより短いという証明が要る。
停止性の証明は通常二段階で書くと便利である。まず、Leanが停止性を検証できるようにする命題を書き、次にそれらを証明する。
そうしないと、命題の証明に多大な労力を注いだ末に、それらが再帰呼び出しがより小さな入力に対して行われていることを示すのに必要なものと少し違うと分かることがある。

{lit}`sorry`タクティクはどのゴールでも、偽のものでも証明できる。
製品のコードや最終的な証明で使うためのものではないが、証明やプログラムを前もって「下書き」する便利な手段である。
{lit}`sorry`を使う定義や定理には警告が付けられる。

{lit}`sorry`を使う{anchorName mergeSortSorry}`mergeSort`の停止性の議論の最初の下書きは、Leanが証明できなかったゴールを{kw}`have`式に写すことで書ける。
Leanでは、{kw}`have`は{kw}`let`に似ている。
{kw}`have`を使うとき、名前は任意である。
通常、{kw}`let`は関心のある値を指す名前を定義するのに使い、{kw}`have`は、Leanが配列の参照が範囲内である証拠や関数が停止する証拠を探すときに見つけられる命題を局所的に証明するのに使う。
```anchor mergeSortSorry
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    have : halves.fst.length < xs.length := by
      sorry
    have : halves.snd.length < xs.length := by
      sorry
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length
```
警告は名前{anchorName mergeSortSorry}`mergeSort`のところに出る。
```anchorWarning mergeSortSorry
declaration uses `sorry`
```
エラーがないので、提案した命題は停止性を示すのに十分である。

証明は補助定理を適用することから始める。
```anchor mergeSortNeedsGte
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    have : halves.fst.length < xs.length := by
      apply splitList_shorter_fst
    have : halves.snd.length < xs.length := by
      apply splitList_shorter_snd
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length
```
どちらの証明も失敗する。{anchorName mergeSortNeedsGte}`splitList_shorter_fst`と{anchorName mergeSortNeedsGte}`splitList_shorter_snd`のどちらも{anchorTerm mergeSortGteStarted}`xs.length ≥ 2`の証明を要求するためである。
```anchorError mergeSortNeedsGte
unsolved goals
α : Type ?u.3
inst✝ : Ord α
xs : List α
h : ¬xs.length < 2
halves : List α × List α := ⋯
⊢ xs.length ≥ 2
```
これで証明を完成させるのに十分かを確かめるには、{lit}`sorry`を使ってそれを加え、エラーがないか調べる。
```anchor mergeSortGteStarted
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    have : xs.length ≥ 2 := by sorry
    have : halves.fst.length < xs.length := by
      apply splitList_shorter_fst
      assumption
    have : halves.snd.length < xs.length := by
      apply splitList_shorter_snd
      assumption
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length
```
ここでもまた、警告だけが出る。
```anchorWarning mergeSortGteStarted
declaration uses `sorry`
```

使えそうな前提が一つある。{lit}`h : ¬List.length xs < 2`で、{kw}`if`から来ている。
明らかに、{anchorTerm mergeSort}`xs.length < 2`でないなら{anchorTerm mergeSort}`xs.length ≥ 2`である。
{anchorTerm mergeSort}`grind`タクティクがこのゴールを解き、プログラムが完成する。

```anchor mergeSort
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    have : xs.length ≥ 2 := by
      grind
    have : halves.fst.length < xs.length := by
      apply splitList_shorter_fst
      assumption
    have : halves.snd.length < xs.length := by
      apply splitList_shorter_snd
      assumption
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length
```

この関数は例で試せる。
```anchor mergeSortRocks
#eval mergeSort ["soapstone", "geode", "mica", "limestone"]
```
```anchorInfo mergeSortRocks
["geode", "limestone", "mica", "soapstone"]
```
```anchor mergeSortNumbers
#eval mergeSort [5, 3, 22, 15]
```
```anchorInfo mergeSortNumbers
[3, 5, 15, 22]
```

# 引き算の繰り返しとしての除算
%%%
tag := "division-as-iterated-subtraction"
%%%

乗算が加算の繰り返しであり、累乗が乗算の繰り返しであるのと同じく、除算は引き算の繰り返しとして理解できる。
{ref "recursive-functions"}[この本で最初に再帰関数を説明した箇所]で、除数が0でないときに停止する除算の版を示したが、Leanはそれを受け付けない。
除算が停止することを証明するには、不等号についての事実を使う必要がある。

Leanはこの除算の定義が停止することを証明できない。
```anchor divTermination (module := Examples.ProgramsProofs.Div)
def div (n k : Nat) : Nat :=
  if n < k then
    0
  else
    1 + div (n - k) k
```

```anchorError divTermination (module := Examples.ProgramsProofs.Div)
fail to show termination for
  div
with errors
failed to infer structural recursion:
Not considering parameter k of div:
  it is unchanged in the recursive calls
Cannot use parameter n:
  failed to eliminate recursive application
    div (n - k) k


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
k n : Nat
h✝ : ¬n < k
⊢ n - k < n
```

これはよいことである。実際、停止しないからである。
{anchorName divTermination (module:=Examples.ProgramsProofs.Div)}`k`が{anchorTerm divTermination (module:=Examples.ProgramsProofs.Div)}`0`のとき、{anchorName divTermination (module:=Examples.ProgramsProofs.Div)}`n`の値が小さくならないので、そのプログラムは無限ループになる。

:::paragraph
{anchorName divRecursiveWithProof (module:=Examples.ProgramsProofs.Div)}`k`が{anchorTerm divRecursiveNeedsProof (module:=Examples.ProgramsProofs.Div)}`0`でない証拠を取るように関数を書き換えると、Leanが停止性を自動で証明できる。

```anchor divRecursiveNeedsProof (module := Examples.ProgramsProofs.Div)
def div (n k : Nat) (ok : k ≠ 0) : Nat :=
  if h : n < k then
    0
  else
    1 + div (n - k) k ok
```
:::

この{anchorName divRecursiveWithProof (module:=Examples.ProgramsProofs.Div)}`div`の定義は、再帰呼び出しごとに一つ目の引数{anchorName divRecursiveWithProof (module:=Examples.ProgramsProofs.Div)}`n`が小さくなるので停止する。
これは{kw}`termination_by`の句で表せる。


```anchor divRecursiveWithProof (module := Examples.ProgramsProofs.Div)
def div (n k : Nat) (ok : k ≠ 0) : Nat :=
  if h : n < k then
    0
  else
    1 + div (n - k) k ok
termination_by n
```


# 練習問題
%%%
tag := "inequalities-exercises"
%%%

次の定理を{tactic}`grind`を使わずに証明せよ。

 * すべての自然数$`n`について$`0 < n + 1`。
 * すべての自然数$`n`について$`0 \leq n`。
 * すべての自然数$`n`と$`k`について$`(n + 1) - (k + 1) = n - k`。
 * すべての自然数$`n`と$`k`について、$`k < n`なら$`n \neq 0`。
 * すべての自然数$`n`について$`n - n = 0`。
 * すべての自然数$`n`と$`k`について、$`n + 1 < k`なら$`n < k`。
