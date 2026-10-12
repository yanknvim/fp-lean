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
The current proof state has one goal remaining:
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

Using {anchorName splitList_shorter_le}`Nat.le_succ_of_le` together with the {lit}`right✝` assumption completes the proof:

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

The next step is to return to the actual theorem that is needed to prove that merge sort terminates: that so long as a list has at least two entries, both results of splitting it are strictly shorter.
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
Pattern matching works just as well in tactic scripts as it does in programs.
Because {anchorName splitList_shorter_1}`lst` has at least two entries, they can be exposed with {kw}`match`, which also refines the type through dependent pattern matching:
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
Simplifying using {anchorName splitList}`splitList` removes {anchorName splitList_shorter_2}`x` and {anchorName splitList_shorter_2}`y`, resulting in the computed lengths of lists each gaining a {anchorTerm le_succ_of_le}`+ 1`:
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
Replacing {anchorTerm splitList_shorter_2b}`simp` with {anchorTerm splitList_shorter_2b}`simp +arith` removes these {anchorTerm le_succ_of_le}`+ 1`s, because {anchorTerm splitList_shorter_2b}`simp +arith` makes use of the fact that {anchorTerm Nat.lt_imp}`n + 1 < m + 1` implies {anchorTerm Nat.lt_imp}`n < m`:
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
This goal now matches {anchorName splitList_shorter}`splitList_shorter_le`, which can be used to conclude the proof:

```anchor splitList_shorter
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := by
  match lst with
  | x :: y :: xs =>
    simp +arith [splitList]
    apply splitList_shorter_le
```

The facts needed to prove that {anchorName mergeSort}`mergeSort` terminates can be pulled out of the resulting {anchorName AndUse}`And`:

```anchor splitList_shorter_sides
theorem splitList_shorter_fst (lst : List α) (h : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length :=
  splitList_shorter lst h |>.left

theorem splitList_shorter_snd (lst : List α) (h : lst.length ≥ 2) :
    (splitList lst).snd.length < lst.length :=
  splitList_shorter lst h |>.right
```

## A Simpler Proof
%%%
tag := "splitList-shorter-le-simpler-proof"
%%%


:::paragraph
Instead of using ordinary induction, {anchorName splitList_shorter_le_funInd1}`splitList_shorter_le` can be proved using functional induction, resulting in one case for each branch of {anchorName splitList}`splitList`:
```anchor splitList_shorter_le_funInd1
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  fun_induction splitList with
  | case1 => skip
  | case2 x xs a b splitEq ih => skip
```
The first case matches the base case of {anchorName splitList}`splitList`.
_Both_ applications of {anchorName splitList}`splitList` have been replaced by the result of this first branch:
```anchorError splitList_shorter_le_funInd1
unsolved goals
case case1
α : Type u_1
⊢ ([], []).fst.length ≤ [].length ∧ ([], []).snd.length ≤ [].length
```
The second case matches the recursive branch of {anchorName splitList}`splitList`.
In addition to the induction hypothesis, the value of the {anchorTerm splitList}`let` in {anchorName splitList}`splitList` is tracked in an assumption:
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

While the second case looks a bit complicated, everything needed to complete the proof is present.
Indeed, {tactic}`grind` can prove both goals immediately:
```anchor splitList_shorter_le_funInd2
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  fun_induction splitList <;> grind
```

# Merge Sort Terminates
%%%
tag := "merge-sort-terminates"
%%%

Merge sort has two recursive calls, one for each sub-list returned by {anchorName splitList}`splitList`.
Each recursive call will require a proof that the length of the list being passed to it is shorter than the length of the input list.
It's usually convenient to write a termination proof in two steps: first, write down the propositions that will allow Lean to verify termination, and then prove them.
Otherwise, it's possible to put a lot of effort into proving the propositions, only to find out that they aren't quite what's needed to establish that the recursive calls are on smaller inputs.

The {lit}`sorry` tactic can prove any goal, even false ones.
It isn't intended for use in production code or final proofs, but it is a convenient way to “sketch out” a proof or program ahead of time.
Any definitions or theorems that use {lit}`sorry` are annotated with a warning.

The initial sketch of {anchorName mergeSortSorry}`mergeSort`'s termination argument that uses {lit}`sorry` can be written by copying the goals that Lean couldn't prove into {kw}`have`-expressions.
In Lean, {kw}`have` is similar to {kw}`let`.
When using {kw}`have`, the name is optional.
Typically, {kw}`let` is used to define names that refer to interesting values, while {kw}`have` is used to locally prove propositions that can be found when Lean is searching for evidence that an array lookup is in-bounds or that a function terminates.
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
The warning is located on the name {anchorName mergeSortSorry}`mergeSort`:
```anchorWarning mergeSortSorry
declaration uses `sorry`
```
Because there are no errors, the proposed propositions are enough to establish termination.

The proofs begin by applying the helper theorems:
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
Both proofs fail, because {anchorName mergeSortNeedsGte}`splitList_shorter_fst` and {anchorName mergeSortNeedsGte}`splitList_shorter_snd` both require a proof that {anchorTerm mergeSortGteStarted}`xs.length ≥ 2`:
```anchorError mergeSortNeedsGte
unsolved goals
α : Type ?u.3
inst✝ : Ord α
xs : List α
h : ¬xs.length < 2
halves : List α × List α := ⋯
⊢ xs.length ≥ 2
```
To check that this will be enough to complete the proof, add it using {lit}`sorry` and check for errors:
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
Once again, there is only a warning.
```anchorWarning mergeSortGteStarted
declaration uses `sorry`
```

There is one promising assumption available: {lit}`h : ¬List.length xs < 2`, which comes from the {kw}`if`.
Clearly, if it is not the case that {anchorTerm mergeSort}`xs.length < 2`, then {anchorTerm mergeSort}`xs.length ≥ 2`.
The {anchorTerm mergeSort}`grind` tactic solves this goal, and the program is now complete:

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

The function can be tested on examples:
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

# Division as Iterated Subtraction
%%%
tag := "division-as-iterated-subtraction"
%%%

Just as multiplication is iterated addition and exponentiation is iterated multiplication, division can be understood as iterated subtraction.
The {ref "recursive-functions"}[very first description of recursive functions in this book] presents a version of division that terminates when the divisor is not zero, but that Lean does not accept.
Proving that division terminates requires the use of a fact about inequalities.

Lean cannot prove that this definition of division terminates:
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

That's a good thing, because it doesn't!
When {anchorName divTermination (module:=Examples.ProgramsProofs.Div)}`k` is {anchorTerm divTermination (module:=Examples.ProgramsProofs.Div)}`0`, value of {anchorName divTermination (module:=Examples.ProgramsProofs.Div)}`n` does not decrease, so the program is an infinite loop.

:::paragraph
Rewriting the function to take evidence that {anchorName divRecursiveWithProof (module:=Examples.ProgramsProofs.Div)}`k` is not {anchorTerm divRecursiveNeedsProof (module:=Examples.ProgramsProofs.Div)}`0` allows Lean to automatically prove termination:

```anchor divRecursiveNeedsProof (module := Examples.ProgramsProofs.Div)
def div (n k : Nat) (ok : k ≠ 0) : Nat :=
  if h : n < k then
    0
  else
    1 + div (n - k) k ok
```
:::

This definition of {anchorName divRecursiveWithProof (module:=Examples.ProgramsProofs.Div)}`div` terminates because the first argument {anchorName divRecursiveWithProof (module:=Examples.ProgramsProofs.Div)}`n` is smaller on each recursive call.
これは{kw}`termination_by`の句で表せる。


```anchor divRecursiveWithProof (module := Examples.ProgramsProofs.Div)
def div (n k : Nat) (ok : k ≠ 0) : Nat :=
  if h : n < k then
    0
  else
    1 + div (n - k) k ok
termination_by n
```


# Exercises
%%%
tag := "inequalities-exercises"
%%%

Prove the following theorems without using {tactic}`grind`:

 * For all natural numbers $`n`, $`0 < n + 1`.
 * For all natural numbers $`n`, $`0 \leq n`.
 * For all natural numbers $`n` and $`k`, $`(n + 1) - (k + 1) = n - k`
 * For all natural numbers $`n` and $`k`, if $`k < n` then $`n \neq 0`
 * For all natural numbers $`n`, $`n - n = 0`
 * For all natural numbers $`n` and $`k`, if $`n + 1 < k` then $`n < k`
