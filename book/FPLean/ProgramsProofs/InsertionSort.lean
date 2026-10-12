module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.InsertionSort"

#doc (Manual) "Insertion Sort and Array Mutation" =>
%%%
tag := "insertion-sort-mutation"
%%%

挿入ソートは、並べ替えの算法として最適な最悪時の時間計算量を持つわけではないが、それでもいくつか役に立つ性質がある。
 * 実装と理解が単純で素直である。
 * その場で動く算法であり、動かすのに追加の空間を要しない。
 * 安定な並べ替えである。
 * 入力がすでにほとんど整列しているときは速い。

その場で動く算法は、Leanのメモリ管理の仕方のために、Leanでは特に役に立つ。
場合によっては、通常なら配列を複製するはずの操作が、変更に最適化される。
これには配列の要素の入れ替えも含まれる。

JavaScript、JVM、.NETを含め、自動のメモリ管理を持つほとんどの言語と実行時システムは、追跡型のガベージコレクションを使う。
メモリを回収する必要が生じると、システムはいくつかの*根*（呼び出しスタックや大域の値など）から始め、ポインタを再帰的にたどってどの値に到達できるかを判断する。
到達できない値は解放され、メモリが空く。

参照カウントは、追跡型のガベージコレクションに代わるもので、Python、Swift、Leanを含む多くの言語で使われている。
参照カウントを使うシステムでは、メモリ内の各オブジェクトが、それへの参照がいくつあるかを追跡するフィールドを持つ。
新しい参照が作られると、カウンタが増やされる。
参照がなくなると、カウンタが減らされる。
カウンタが0になると、そのオブジェクトはすぐに解放される。

参照カウントには、追跡型のガベージコレクタに比べて大きな欠点が一つある。循環参照がメモリの漏れにつながりうることである。
オブジェクト$`A`がオブジェクト$`B`を参照し、$`B`が$`A`を参照していると、プログラムの他のどこも$`A`も$`B`も参照していなくても、それらは決して解放されない。
循環参照は、制御されない再帰か、可変の参照から生じる。
Leanはどちらも支えないので、循環参照を作ることは不可能である。

参照カウントのおかげで、Leanの実行時システムがデータ構造を確保・解放するための原始的な操作は、参照カウントが0になろうとしているかを調べ、新しいオブジェクトを確保する代わりに既存のオブジェクトを使い回せる。
これは大きな配列を扱うときに特に重要である。


Leanの配列に対する挿入ソートの実装は、次の基準を満たすべきである。
 1. Leanがその関数を{kw}`partial`の注記なしに受け付けるべきである。
 2. 他に参照のない配列を渡されたら、新しい配列を確保するのではなく、その配列をその場で変更すべきである。

一つ目の基準は確かめやすい。Leanがその定義を受け付ければ、満たされている。
しかし二つ目は、それを試す手段が要る。
Leanには{anchorName dbgTraceIfSharedSig}`dbgTraceIfShared`という組み込みの関数があり、次のシグネチャを持つ。
```anchor dbgTraceIfSharedSig
#check dbgTraceIfShared
```
```anchorInfo dbgTraceIfSharedSig
dbgTraceIfShared.{u} {α : Type u} (s : String) (a : α) : α
```
これは文字列と値を引数に取り、その値への参照が二つ以上あるならその文字列を使ったメッセージを標準エラーに出力し、その値を返す。
厳密に言えば、これは純粋な関数ではない。
しかし、開発中に、ある関数が実際にメモリを確保して複製するのではなく使い回せることを確かめるためだけに使うものである。

{anchorName dbgTraceIfSharedSig}`dbgTraceIfShared`の使い方を学ぶときは、{kw}`#eval`がコンパイル済みのコードよりもずっと多くの値が共有されていると報告することを知っておくことが重要である。
これは紛らわしいことがある。
エディタで試すのではなく、{lit}`lake`で実行ファイルを組み立てることが重要である。

挿入ソートは二つのループから成る。
外側のループは、並べ替える配列に沿ってポインタを左から右へ動かす。
繰り返しごとに、ポインタより左の配列の範囲は整列しており、右の範囲はまだ整列していないかもしれない。
内側のループは、ポインタが指す要素を取り、適切な位置が見つかってループの不変条件が回復するまでそれを左へ動かす。
言い換えれば、繰り返しごとに、配列の次の要素を整列済みの範囲の適切な位置に挿入する。

# 内側のループ
%%%
tag := "inner-insertion-sort-loop"
%%%

挿入ソートの内側のループは、配列と、挿入する要素の添字を引数に取る末尾再帰関数として実装できる。
挿入する要素は、左隣の要素が小さいか、配列の先頭に達するまで、繰り返し左隣の要素と入れ替えられる。
内側のループは、配列の参照に使う{anchorName insertSorted}`Fin`の中にある{anchorName insertionSortLoop}`Nat`について構造的再帰である。

```anchor insertSorted
def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, _⟩ =>
    match Ord.compare arr[i'] arr[i] with
    | .lt | .eq => arr
    | .gt =>
      insertSorted (arr.swap i' i) ⟨i', by grind⟩
```
添字{anchorName insertSorted}`i`が{anchorTerm insertSorted}`0`なら、整列済みの範囲に挿入する要素がその範囲の先頭に達しており、最も小さい。
添字が{anchorTerm insertSorted}`i' + 1`なら、{anchorName insertSorted}`i'`にある要素を{anchorName insertSorted}`i`にある要素と比べるべきである。
{anchorName insertSorted}`i`は{anchorTerm insertSorted}`Fin arr.size`だが、{anchorName insertSorted}`i'`は{anchorName insertSorted}`i`の{anchorName names}`val`フィールドから得られるので単なる{anchorName insertionSortLoop}`Nat`であることに注意せよ。
それでも、配列の参照記法を調べるのに使う証明の自動化には線形整数算術の解決器が含まれているので、{anchorName insertSorted}`i'`は自動で添字として使える。

二つの要素が参照されて比べられる。
左の要素が挿入する要素以下なら、ループは終わり、不変条件が回復している。
左の要素が挿入する要素より大きいなら、それらの要素が入れ替えられ、内側のループが再び始まる。
{anchorName names}`Array.swap`は両方の添字を{anchorName names}`Nat`として取り、配列の参照と同じタクティクを裏で使ってそれらが範囲内であることを保証する。

それでも、再帰呼び出しに使う{anchorName names}`Fin`には、二つの要素を入れ替えた結果で{anchorName insertSorted}`i'`が範囲内であるという証明が要る。
{anchorTerm insertSorted}`grind`タクティクのデータベースには、配列の二つの要素を入れ替えてもその大きさが変わらないという事実が入っている。
これを、元の配列で{anchorTerm insertSorted}`i' + 1`が範囲内であるという事実と合わせると、{anchorTerm insertSorted}`grind`は入れ替えの後に{anchorName insertSorted}`i'`が範囲内であると結論できる。


# 外側のループ
%%%
tag := "outer-insertion-sort-loop"
%%%

挿入ソートの外側のループはポインタを左から右へ動かし、繰り返しごとに{anchorName insertionSortLoop}`insertSorted`を呼び出して、ポインタにある要素を配列の正しい位置に挿入する。
このループの基本の形は{anchorTerm etc}`Array.map`の実装に似ている。
```anchor insertionSortLoopTermination
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
```
再帰呼び出しごとに小さくなる引数がないので、エラーになる。
```anchorError insertionSortLoopTermination
fail to show termination for
  insertionSortLoop
with errors
failed to infer structural recursion:
Not considering parameter α of insertionSortLoop:
  it is unchanged in the recursive calls
Not considering parameter #2 of insertionSortLoop:
  it is unchanged in the recursive calls
Cannot use parameter arr:
  the type Array α does not have a `.brecOn` recursor
Cannot use parameter i:
  failed to eliminate recursive application
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
            arr i #1
1) 569:4-55   ? ?  ?

#1: arr.size - i

Please use `termination_by` to specify a decreasing measure.
```
Leanは、繰り返しごとに一定の上限に向かって増える{anchorName insertionSortLoop}`Nat`が停止する関数につながることを証明できるが、この関数には一定の上限がない。繰り返しごとに配列が{anchorName insertionSortLoop}`insertSorted`を呼び出した結果で置き換えられるためである。

停止性の証明を組み立てる前に、{kw}`partial`修飾子を付けて定義を試し、期待どおりの答えを返すことを確かめると便利である。

```anchor partialInsertionSortLoop
partial def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
```
```anchor insertionSortPartialOne
#eval insertionSortLoop #[5, 17, 3, 8] 0
```
```anchorInfo insertionSortPartialOne
#[3, 5, 8, 17]
```
```anchor insertionSortPartialTwo
#eval insertionSortLoop #["metamorphic", "igneous", "sedimentary"] 0
```
```anchorInfo insertionSortPartialTwo
#["igneous", "metamorphic", "sedimentary"]
```

## Termination
%%%
tag := "insertionSortLoop-termination"
%%%

ここでもまた、処理する配列の大きさと添字の差が再帰呼び出しごとに小さくなるので、この関数は停止する。
しかし今回は、Leanは{kw}`termination_by`を受け付けない。
```anchor insertionSortLoopProof1
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i
```
```anchorError insertionSortLoopProof1
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Nat
h : i < arr.size
⊢ (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i
```
問題は、{anchorName insertionSortLoop}`insertSorted`が、渡されたものと同じ大きさの配列を返すことをLeanが知る手立てがないことである。
{anchorName insertionSortLoop}`insertionSortLoop`が停止することを証明するには、まず{anchorName insertionSortLoop}`insertSorted`が配列の大きさを変えないことを証明する必要がある。
エラーメッセージから証明されていない停止条件を関数に写し、{anchorTerm insertionSortLoopSorry}`sorry`で「証明」すると、その関数を一時的に受け付けさせられる。
```anchor insertionSortLoopSorry
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
      sorry
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i
```
```anchorWarning insertionSortLoopSorry
declaration uses `sorry`
```

{anchorName insertionSortLoop}`insertSorted`は挿入する要素の添字について構造的再帰なので、証明はその添字についての帰納法によるべきである。
基底の場合は、配列が変わらずに返るので、その長さはもちろん変わらない。
帰納法の段階では、帰納法の仮定は、次に小さい添字での再帰呼び出しが配列の長さを変えないというものである。
考えるべき場合は二つある。要素が整列済みの範囲に完全に挿入されて配列が変わらずに返る場合（この場合も長さは変わらない）か、再帰呼び出しの前に要素が次のものと入れ替えられる場合である。
しかし、配列の二つの要素を入れ替えてもその大きさは変わらず、帰納法の仮定は、次の添字での再帰呼び出しが引数と同じ大きさの配列を返すことを述べている。
したがって、大きさは変わらないままである。

この英語の定理の言明をLeanに移し、この章の技法を使って進めれば、基底の場合を証明し、帰納法の段階で進展させるのに十分である。
```anchor insert_sorted_size_eq_0
theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  match i with
  | ⟨j, isLt⟩ =>
    induction j with
    | zero => simp [insertSorted]
    | succ j' ih =>
      simp [insertSorted]
```
帰納法の段階で{anchorName insert_sorted_size_eq_0}`insertSorted`を使って単純化すると、{anchorName insert_sorted_size_eq_0}`insertSorted`のパターンマッチングが現れる。
```anchorError insert_sorted_size_eq_0
unsolved goals
case succ
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Fin arr.size
j' : Nat
ih : ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.size
isLt : j' + 1 < arr.size
⊢ (match compare arr[j'] arr[j' + 1] with
    | Ordering.lt => arr
    | Ordering.eq => arr
    | Ordering.gt => insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size =
  arr.size
```
{kw}`if`や{kw}`match`を含むゴールに直面したとき、{anchorTerm insert_sorted_size_eq_1}`split`タクティク（マージソートの定義で使った{anchorName splitList (module := Examples.ProgramsProofs.Inequalities)}`splitList`関数と混同しないこと）は、ゴールを制御の流れの道筋ごとに一つの新しいゴールで置き換える。
```anchor insert_sorted_size_eq_1
theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  match i with
  | ⟨j, isLt⟩ =>
    induction j with
    | zero => simp [insertSorted]
    | succ j' ih =>
      simp [insertSorted]
      split
```
ある言明が*どう*証明されたかは通常問題ではなく、証明された*こと*だけが問題なので、Leanの出力では証明が通常{lit}`⋯`で置き換えられる。
さらに、各新しいゴールには、どの枝がそのゴールにつながったかを示す前提があり、この場合は{lit}`heq✝`という名前である。
```anchorError insert_sorted_size_eq_1
unsolved goals
case h_1
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Fin arr.size
j' : Nat
ih : ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.size
isLt : j' + 1 < arr.size
x✝ : Ordering
heq✝ : compare arr[j'] arr[j' + 1] = Ordering.lt
⊢ arr.size = arr.size

case h_2
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Fin arr.size
j' : Nat
ih : ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.size
isLt : j' + 1 < arr.size
x✝ : Ordering
heq✝ : compare arr[j'] arr[j' + 1] = Ordering.eq
⊢ arr.size = arr.size

case h_3
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Fin arr.size
j' : Nat
ih : ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.size
isLt : j' + 1 < arr.size
x✝ : Ordering
heq✝ : compare arr[j'] arr[j' + 1] = Ordering.gt
⊢ (insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size = arr.size
```
二つの簡単な場合の証明を書く代わりに、{anchorTerm insert_sorted_size_eq_2}`split`の後に{anchorTerm insert_sorted_size_eq_2}`<;> try rfl`を加えると、その二つの素直な場合がすぐに消え、ゴールが一つだけ残る。
```anchor insert_sorted_size_eq_2
theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  match i with
  | ⟨j, isLt⟩ =>
    induction j with
    | zero => simp [insertSorted]
    | succ j' ih =>
      simp [insertSorted]
      split <;> try rfl
```
```anchorError insert_sorted_size_eq_2
unsolved goals
case h_3
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Fin arr.size
j' : Nat
ih : ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.size
isLt : j' + 1 < arr.size
x✝ : Ordering
heq✝ : compare arr[j'] arr[j' + 1] = Ordering.gt
⊢ (insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size = arr.size
```

残念ながら、帰納法の仮定はこのゴールを証明するのに十分な強さではない。
帰納法の仮定は、{anchorName insert_sorted_size_eq_3}`arr`に{anchorName insert_sorted_size_eq_3}`insertSorted`を呼ぶと大きさが変わらないことを述べているが、証明のゴールは、入れ替えた結果での再帰呼び出しの結果が大きさを変えないことを示すことである。
証明をうまく完成させるには、より小さい添字とともに{anchorName insert_sorted_size_eq_3}`insertSorted`に渡される*どの*配列でも働く帰納法の仮定が要る。

{anchorTerm insert_sorted_size_eq_3}`induction`タクティクの{anchorTerm insert_sorted_size_eq_3}`generalizing`の選択肢を使うと、強い帰納法の仮定を得られる。
この選択肢は、文脈からの追加の前提を、基底の場合、帰納法の仮定、帰納法の段階で示すゴールを生成するのに使う言明に持ち込む。
{anchorName insert_sorted_size_eq_3}`arr`について一般化すると、より強い仮定になる。
```anchor insert_sorted_size_eq_3
theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  match i with
  | ⟨j, isLt⟩ =>
    induction j generalizing arr with
    | zero => simp [insertSorted]
    | succ j' ih =>
      simp [insertSorted]
      split <;> try rfl
```
得られるゴールでは、{anchorName insert_sorted_size_eq_3}`arr`が帰納法の仮定の「すべての」という言明の一部になっている。
```anchorError insert_sorted_size_eq_3
unsolved goals
case h_3
α : Type u_1
inst✝ : Ord α
j' : Nat
ih : ∀ (arr : Array α) (i : Fin arr.size) (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.size
arr : Array α
i : Fin arr.size
isLt : j' + 1 < arr.size
x✝ : Ordering
heq✝ : compare arr[j'] arr[j' + 1] = Ordering.gt
⊢ (insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size = arr.size
```

:::paragraph
しかし、この証明全体が手に負えなくなってきている。
次の段階は、入れ替えの結果の長さを表す変数を導入し、それが{anchorTerm insert_sorted_size_eq_3}`arr.size`と等しいことを示し、次にその変数が再帰呼び出しの結果の配列の長さとも等しいことを示すことになる。
これらの等しさの言明を鎖のようにつないでゴールを証明できる。
しかし、関数による帰納法を使うほうがずっと簡単である。
```anchor insert_sorted_size_eq_funInd1
theorem insert_sorted_size_eq [Ord α]
    (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  fun_induction insertSorted with
  | case1 arr => skip
  | case2 arr i this isLt => skip
  | case3 arr i this isEq => skip
  | case4 arr i this isGt ih => skip
```
一つ目のゴールは添字{anchorTerm insertSorted}`0`の場合である。
ここでは配列が変更されないので、その大きさが変わらないことを証明するのに複雑な段階は要らない。
```anchorError insert_sorted_size_eq_funInd1
unsolved goals
case case1
α : Type u_1
inst✝ : Ord α
arr✝ arr : Array α
isLt✝ : 0 < arr.size
⊢ arr.size = arr.size
```
次の二つのゴールは同じで、要素の比較の{anchorName insertSorted}`.lt`と{anchorName insertSorted}`.eq`の場合を扱う。
局所的な前提{anchorName insert_sorted_size_eq_funInd1}`isLt`と{anchorName insert_sorted_size_eq_funInd1}`isEq`により、{anchorTerm insertSorted}`match`の正しい枝を選べる。
```anchorError insert_sorted_size_eq_funInd1
unsolved goals
case case2
α : Type u_1
inst✝ : Ord α
arr✝ arr : Array α
i : Nat
this : i + 1 < arr.size
isLt : compare arr[i] arr[⟨i.succ, this⟩] = Ordering.lt
⊢ (match compare arr[i] arr[⟨i.succ, this⟩] with
    | Ordering.lt => arr
    | Ordering.eq => arr
    | Ordering.gt => insertSorted (arr.swap i ↑⟨i.succ, this⟩ ⋯ ⋯) ⟨i, ⋯⟩).size =
  arr.size
```
```anchorError insert_sorted_size_eq_funInd1
unsolved goals
case case3
α : Type u_1
inst✝ : Ord α
arr✝ arr : Array α
i : Nat
this : i + 1 < arr.size
isEq : compare arr[i] arr[⟨i.succ, this⟩] = Ordering.eq
⊢ (match compare arr[i] arr[⟨i.succ, this⟩] with
    | Ordering.lt => arr
    | Ordering.eq => arr
    | Ordering.gt => insertSorted (arr.swap i ↑⟨i.succ, this⟩ ⋯ ⋯) ⟨i, ⋯⟩).size =
  arr.size
```
最後の場合は、{anchorTerm insertSorted}`match`を簡約した後、挿入の次の段階が配列の大きさを保つことを証明する作業が残る。
特に、帰納法の仮定は、次の段階の大きさが入れ替えの結果の大きさと等しいことを述べているが、望む結論はそれが元の配列の大きさと等しいことである。
```anchorError insert_sorted_size_eq_funInd1
unsolved goals
case case4
α : Type u_1
inst✝ : Ord α
arr✝ arr : Array α
i : Nat
this : i + 1 < arr.size
isGt : compare arr[i] arr[⟨i.succ, this⟩] = Ordering.gt
ih : (insertSorted (arr.swap i ↑⟨i.succ, this⟩ ⋯ ⋯) ⟨i, ⋯⟩).size = (arr.swap i ↑⟨i.succ, this⟩ ⋯ ⋯).size
⊢ (match compare arr[i] arr[⟨i.succ, this⟩] with
    | Ordering.lt => arr
    | Ordering.eq => arr
    | Ordering.gt => insertSorted (arr.swap i ↑⟨i.succ, this⟩ ⋯ ⋯) ⟨i, ⋯⟩).size =
  arr.size
```
:::

:::paragraph
{tactic}`grind`タクティクが四つの場合をすべて片付けられる。
```anchor insert_sorted_size_eq_funInd
theorem insert_sorted_size_eq [Ord α]
    (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  fun_induction insertSorted <;> grind
```
:::

:::paragraph
この証明を使って、{anchorName insertionSortLoopSorry}`insertionSortLoop`の{anchorTerm insertionSortLoopSorry}`sorry`を置き換えられる。
特に、この定理により{anchorTerm insertionSortLoop}`grind`が成功する。
```anchor insertionSortLoop
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
      grind [insert_sorted_size_eq]
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i
```
:::


# 駆動する関数
%%%
tag := "insertion-sort-driver-function"
%%%

挿入ソート自体は{anchorName insertionSort}`insertionSortLoop`を呼び出し、配列の整列済みの範囲と未整列の範囲を区切る添字を{anchorTerm insertionSort}`0`に初期化する。

```anchor insertionSort
def insertionSort [Ord α] (arr : Array α) : Array α :=
   insertionSortLoop arr 0
```

いくつか簡単に試すと、この関数が少なくとも明らかに間違ってはいないことが分かる。
```anchor insertionSortNums
#eval insertionSort #[3, 1, 7, 4]
```
```anchorInfo insertionSortNums
#[1, 3, 4, 7]
```
```anchor insertionSortStrings
#eval insertionSort #[ "quartz", "marble", "granite", "hematite"]
```
```anchorInfo insertionSortStrings
#["granite", "hematite", "marble", "quartz"]
```

# これは本当に挿入ソートか
%%%
tag := "insertion-sort-in-place"
%%%


挿入ソートは、その場で動く並べ替えの算法として*定義されている*。
最悪時の実行時間が二次であるにもかかわらずこれが役に立つのは、追加の空間を確保せず、ほとんど整列したデータを効率よく扱う、安定な並べ替えの算法だからである。
内側のループの繰り返しごとに新しい配列を確保するなら、その算法は*本当には*挿入ソートではない。

{anchorName names}`Array.set`や{anchorName names}`Array.swap`のようなLeanの配列の操作は、その配列の参照カウントが1より大きいかどうかを調べる。
そうなら、その配列はコードの複数の部分から見えるので、複製せねばならない。
そうしなければ、Leanはもはや純粋な関数型言語ではなくなる。
しかし、参照カウントがちょうど1のときは、その値を見る可能性のある他のものがない。
このような場合、配列の原始的な操作はその配列をその場で変更する。
プログラムの他の部分が知らないことは、それらを害さない。

Leanの証明の論理は、その下の実装ではなく、純粋な関数型プログラムの水準で働く。
つまり、あるプログラムが不必要にデータを複製しているかを見つける最良の方法は、それを試すことである。
変更したい各箇所に{anchorName dbgTraceIfSharedSig}`dbgTraceIfShared`の呼び出しを加えると、その値への参照が二つ以上あるときに与えたメッセージが{lit}`stderr`に出力される。

挿入ソートには、変更ではなく複製をする危険がある箇所がちょうど一つある。{anchorName names}`Array.swap`の呼び出しである。
{anchorTerm insertSorted}`arr.swap i' i`を{anchorTerm InstrumentedInsertionSort (module := Examples.ProgramsProofs.InstrumentedInsertionSort)}`(dbgTraceIfShared "array to swap" arr).swap i' i`に置き換えると、配列を変更できないときに常に{lit}`shared RC array to swap`が出力される。
しかし、このプログラムの変更は証明も変える。追加の関数の呼び出しがあるためである。
{anchorName dbgTraceIfSharedSig}`dbgTraceIfShared`がその引数の長さを保つという局所的な前提を加え、それをいくつかの{anchorTerm InstrumentedInsertionSort (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`grind`の呼び出しに加えれば、プログラムと証明を直すのに十分である。

挿入ソートの計装済みの完全なコードは次のとおりである。
```anchor InstrumentedInsertionSort (module := Examples.ProgramsProofs.InstrumentedInsertionSort)
def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, _⟩ =>
    have : i' < arr.size := by
      grind
    match Ord.compare arr[i'] arr[i] with
    | .lt | .eq => arr
    | .gt =>
      have : (dbgTraceIfShared "array to swap" arr).size = arr.size := by
        grind [dbgTraceIfShared]
      insertSorted
        ((dbgTraceIfShared "array to swap" arr).swap i' i)
        ⟨i', by grind [dbgTraceIfShared]⟩

theorem insert_sorted_size_eq [Ord α]
    (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  fun_induction insertSorted <;> grind [dbgTraceIfShared]

def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
      grind [insert_sorted_size_eq]
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i

def insertionSort [Ord α] (arr : Array α) : Array α :=
  insertionSortLoop arr 0
```

計装が実際に働くかを確かめるには、少し工夫が要る。
第一に、Leanのコンパイラは、関数呼び出しの引数がすべてコンパイル時に分かっていると、その呼び出しを積極的に最適化で取り除く。
{anchorName InstrumentedInsertionSort (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`insertionSort`を大きな配列に適用するプログラムを単に書くだけでは足りない。得られるコンパイル済みのコードが、整列済みの配列を定数として含むだけになることがあるためである。
コンパイラが並べ替えの手続きを最適化で取り除かないようにする最も簡単な方法は、配列を{anchorName getLines (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`stdin`から読むことである。
第二に、コンパイラは到達しないコードの除去を行う。
{kw}`let`で束縛した変数が決して使われないなら、プログラムに余分な{kw}`let`を加えても、動くコードでの参照が増えるとは限らない。
余分な参照が完全に取り除かれないようにするには、その余分な参照が何らかの形で使われるようにすることが重要である。

計装を試す最初の段階は、標準入力から行の配列を読む{anchorName getLines (module := Examples.ProgramsProofs.InstrumentedInsertionSort)}`getLines`を書くことである。
```anchor getLines (module := Examples.ProgramsProofs.InstrumentedInsertionSort)
def getLines : IO (Array String) := do
  let stdin ← IO.getStdin
  let mut lines : Array String := #[]
  let mut currLine ← stdin.getLine
  while !currLine.isEmpty do
     -- Drop trailing newline:
    lines := lines.push (currLine.dropEnd 1).copy
    currLine ← stdin.getLine
  pure lines
```
{anchorName various (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`IO.FS.Stream.getLine`は、末尾の改行を含む完全な一行のテキストを返す。
ファイルの終わりに達すると{anchorTerm mains (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`""`を返す。

次に、別々の{anchorName main (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`main`の手続きが二つ要る。
どちらも並べ替える配列を標準入力から読み、{anchorName mains (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`insertionSort`の呼び出しがコンパイル時に戻り値で置き換えられないようにする。
どちらも次にコンソールへ出力し、{anchorName insertionSort}`insertionSort`の呼び出しが最適化で完全に取り除かれないようにする。
一方は整列済みの配列だけを出力し、他方は整列済みの配列と元の配列の両方を出力する。
二つ目の関数は、{anchorName names}`Array.swap`が新しい配列を確保せねばならなかったという警告を引き起こすはずである。
```anchor mains (module := Examples.ProgramsProofs.InstrumentedInsertionSort)
def mainUnique : IO Unit := do
  let lines ← getLines
  for line in insertionSort lines do
    IO.println line

def mainShared : IO Unit := do
  let lines ← getLines
  IO.println "--- Sorted lines: ---"
  for line in insertionSort lines do
    IO.println line

  IO.println ""
  IO.println "--- Original data: ---"
  for line in lines do
    IO.println line
```

実際の{anchorName main (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`main`は、与えられたコマンドライン引数に基づいて二つのmainの動作の一方を選ぶだけである。
```anchor main (module := Examples.ProgramsProofs.InstrumentedInsertionSort)
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--shared"] => mainShared; pure 0
  | ["--unique"] => mainUnique; pure 0
  | _ =>
    IO.println "Expected either \"--shared\" or \"--unique\""
    pure 1
```

引数なしで実行すると、期待どおりの使い方の情報が出る。
```interaction «sort-sharing» "sort-demo"
{ command := "sort",
  script := #[
    .expect "Expected either \"--shared\" or \"--unique\"",
    .exitCode 1] }
---
$ sort
< Expected either "--shared" or "--unique"
```

ファイル{lit}`test-data`には次の岩石が入っている。
```file «sort-sharing» "sort-demo/test-data"
schist
feldspar
diorite
pumice
obsidian
shale
gneiss
marble
flint
```

計装済みの挿入ソートをこれらの岩石に使うと、それらがアルファベット順に表示される。
```commands «sort-sharing» "sort-demo"
$ sort --unique < test-data
diorite
feldspar
flint
gneiss
marble
obsidian
pumice
schist
shale
```

しかし、元の配列への参照を保持する版では、最初の{anchorName names}`Array.swap`の呼び出しから{lit}`stderr`への通知（つまり{lit}`shared RC array to swap`）が出る。
```commands «sort-sharing» "sort-demo"
$ sort --shared < test-data
--- Sorted lines: ---
diorite
feldspar
flint
gneiss
marble
obsidian
pumice
schist
shale

--- Original data: ---
schist
feldspar
diorite
pumice
obsidian
shale
gneiss
marble
flint
shared RC array to swap
```
{lit}`shared RC`の通知が一つしか出ないということは、配列が一度しか複製されないことを意味する。
{anchorName names}`Array.swap`の呼び出しで生じた複製自体が一意なので、それ以上複製する必要がないためである。
命令型言語では、配列を参照で渡す前に明示的に複製するのを忘れると、微妙な不具合が生じうる。
{lit}`sort --shared`を実行すると、Leanのプログラムの純粋な関数型としての意味を保つために必要なだけ配列が複製され、それ以上は複製されない。


# 変更のその他の機会
%%%
tag := none
%%%

参照が一意のときに複製の代わりに変更を使うのは、配列の更新の演算子に限らない。
Leanはまた、参照カウントが0になろうとしているコンストラクタを「再利用」しようとし、新しいデータを確保する代わりにそれを使い回す。
つまりたとえば、{anchorName names}`List.map`は、誰も気づきえない場合には、連結リストをその場で変更する。
Leanのコードで頻繁に実行されるループを最適化するうえで最も重要な段階の一つは、変更するデータが複数の場所から参照されていないことを確かめることである。

# 練習問題
%%%
tag := "insertion-sort-exercises"
%%%


 * 配列を反転する関数を書け。入力の配列の参照カウントが1なら、自分の関数が新しい配列を確保しないことを試して確かめよ。

 * 配列に対するマージソートかクイックソートのどちらかを実装せよ。自分の実装が停止することを証明し、予想より多くの配列を確保しないことを試して確かめよ。これは難しい練習問題である。
