module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Induction"

#doc (Manual) "Interlude: Tactics, Induction, and Proofs" =>
%%%
tag := "tactics-induction-proofs"
number := false
htmlSplit := .never
%%%

# 証明とユーザーインターフェースについての注意
%%%
tag := "proofs-and-uis"
%%%

本書では、証明は一度に書き上げてLeanに提出し、Leanが残っている作業を説明するエラーメッセージで応答する、という形で説明している。
実際にLeanとやり取りする過程は、ずっと快適である。
カーソルを動かすとその位置の証明についての情報が得られ、証明を楽にする対話的な機能も数多くある。
詳しくは、使っているLeanの開発環境のドキュメントを参照してほしい。

本書のように、証明を少しずつ組み立て、その結果のメッセージを示す進め方は、証明を書いている間にLeanが返す対話的なフィードバックの種類を示している。達人が使う進め方よりずっと遅いが、この形で説明している。
同時に、不完全な証明が完成に近づいていく様子を見ることは、証明を理解する上で役に立つ。
証明を書く力がつくにつれ、Leanのフィードバックは誤りの指摘というより、自分の思考を支えるものに感じられるようになる。
対話的な進め方を身につけることは非常に重要である。

# 再帰と帰納法
%%%
tag := "recursion-vs-induction"
%%%

前の章の{anchorName plusR_succ_left (module := Examples.DependentTypes.Pitfalls)}`plusR_succ_left`と{anchorName plusR_zero_left_thm (module:=Examples.DependentTypes.Pitfalls)}`plusR_zero_left`という関数は、二つの見方ができる。
一方では、他の再帰関数がリストや文字列などのデータ構造を組み立てるのと同じように、命題の証拠を組み立てる再帰関数である。
もう一方では、*数学的帰納法*による証明に相当する。

数学的帰納法は、*すべての*自然数について主張を証明する技法で、二つの段階から成る。
 1. $`0`について主張が成り立つことを示す。これを*基底ケース*と呼ぶ。
 2. 任意に選んだ数$`n`について主張が成り立つと仮定したうえで、$`n + 1`について成り立つことを示す。これを*帰納法の段階*と呼ぶ。$`n`について主張が成り立つという仮定を*帰納法の仮定*と呼ぶ。

*すべての*自然数について主張を確かめることはできないので、帰納法は、原理上は任意の自然数について展開できる証明を書く手段を与える。
たとえば、3について具体的な証明が欲しければ、まず基底ケースを使い、次に帰納法の段階を三度使って、0、1、2、そして最後に3について主張を示せばよい。
こうして、すべての自然数について主張が証明される。

# inductionタクティク
%%%
tag := "induction-tactic"
%%%

{anchorName plusR_zero_left_done (module:=Examples.DependentTypes.Pitfalls)}`congrArg`のような補助関数を使って帰納法の証明を再帰関数として書くと、証明の意図をうまく表せないことがある。
再帰関数は確かに帰納法の構造を持つが、証明の*符号化*として捉えるべきだろう。
さらに、Leanのタクティクの仕組みには、再帰関数を明示的に書くときには得られない、証明の組み立てを自動化する余地がいろいろある。
Leanには、帰納法による証明を一つのタクティクブロックでやり切れる{kw}`induction`タクティクがある。
舞台裏では、Leanが帰納法の使用に対応する再帰関数を組み立てる。

{kw}`induction`タクティクで{anchorName plusR_zero_left_done (module:=Examples.DependentTypes.Pitfalls)}`plusR_zero_left`を証明するには、まずシグネチャを書く（これは本当に証明なので{kw}`theorem`を使う）。
次に、定義の本体として{anchorTerm plusR_ind_zero_left_1}`by induction k`を使う。
```anchor plusR_ind_zero_left_1
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k
```
すると、ゴールが二つあるというメッセージが出る。
```anchorError plusR_ind_zero_left_1
unsolved goals
case zero
⊢ 0 = Nat.plusR 0 0

case succ
n✝ : Nat
a✝ : n✝ = Nat.plusR 0 n✝
⊢ n✝ + 1 = Nat.plusR 0 (n✝ + 1)
```
タクティクブロックは、Leanの型検査器がファイルを処理している間に走るプログラムで、ずっと強力なCのプリプロセッサマクロのようなものである。
タクティクが実際のプログラムを生成する。

タクティク言語では、ゴールが複数あることがある。
各ゴールは、型と前提から成る。
これらはアンダースコアを穴埋めに使うのと似ている。ゴールの型が証明すべきものを表し、前提がその時点で使えるものを表す。
{lit}`case zero`のゴールには前提がなく、型は{anchorTerm others}`Nat.zero = Nat.plusR 0 Nat.zero`である。これは定理の主張の{anchorName plusR_ind_zero_left_1}`k`を{anchorTerm others}`0`に置き換えたものである。
{lit}`case succ`のゴールには、{lit}`n✝`と{lit}`n_ih✝`という二つの前提がある。
舞台裏では、{anchorTerm plusR_ind_zero_left_1}`induction`タクティクが全体の型を絞り込む依存パターンマッチを作り、{lit}`n✝`はそのパターンにおける{anchorName others}`Nat.succ`の引数を表す。
前提{lit}`n_ih✝`は、生成された関数を{lit}`n✝`に対して再帰的に呼び出した結果を表す。
その型は、定理の全体の型の{anchorName plusR_ind_zero_left_1}`k`を{lit}`n✝`に置き換えたものである。
{lit}`case succ`のゴールとして満たすべき型は、定理全体の主張の{anchorName plusR_ind_zero_left_1}`k`を{lit}`Nat.succ n✝`に置き換えたものである。

{anchorTerm plusR_ind_zero_left_1}`induction`タクティクで生じる二つのゴールは、数学的帰納法の説明における基底ケースと帰納法の段階に対応する。
基底ケースが{lit}`case zero`である。
{lit}`case succ`では、{lit}`n_ih✝`が帰納法の仮定にあたり、{lit}`case succ`全体が帰納法の段階である。

証明を書く次の段階は、二つのゴールを順に扱うことである。
{kw}`do`ブロックで「何もしない」ことを表すのに{anchorTerm others}`pure ()`が使えるのと同じように、タクティク言語には何もしない{kw}`skip`という文がある。
Leanの構文がタクティクを要求するのに、どれを使うべきかまだ分からないときに使える。
{kw}`induction`の文の末尾に{kw}`with`を付けると、パターンマッチングに似た構文になる。
```anchor plusR_ind_zero_left_2a
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => skip
  | succ n ih => skip
```
二つの{kw}`skip`の文にはそれぞれメッセージが対応する。
一つ目が基底ケースを示す。
```anchorError plusR_ind_zero_left_2a
unsolved goals
case zero
⊢ 0 = Nat.plusR 0 0
```
二つ目が帰納法の段階を示す。
```anchorError plusR_ind_zero_left_2b
unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ n + 1 = Nat.plusR 0 (n + 1)
```
帰納法の段階では、ダガー付きの参照できない名前が、{lit}`succ`の後に与えた名前、つまり{anchorName plusR_ind_zero_left_2a}`n`と{anchorName plusR_ind_zero_left_2a}`ih`に置き換わっている。

{kw}`induction`{lit}` ...`{kw}`with`の後に続く場合はパターンではない。ゴールの名前と、0個以上の名前から成る。
その名前はゴールで導入される前提に使う。ゴールが導入する数より多くの名前を与えるとエラーになる。
```anchor plusR_ind_zero_left_3
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => skip
  | succ n ih lots of names => skip
```
```anchorError plusR_ind_zero_left_3
Too many variable names provided at alternative `succ`: 5 provided, but 2 expected
```

基底ケースに注目すると、{kw}`rfl`タクティクは{kw}`induction`タクティクの中でも、再帰関数の中と同じように働く。
```anchor plusR_ind_zero_left_4
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih => skip
```
再帰関数版の証明では、型注釈によって期待される型が分かりやすくなっていた。
タクティク言語には、ゴールを解きやすい形に変換する具体的な方法がいくつかある。
{kw}`unfold`タクティクは、定義済みの名前をその定義で置き換える。
```anchor plusR_ind_zero_left_5
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold Nat.plusR
```
これで、ゴールの等式の右辺は{anchorTerm others}`Nat.plusR 0 (Nat.succ n)`ではなく{anchorTerm others}`Nat.plusR 0 n + 1`になった。
```anchorError plusR_ind_zero_left_5
unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ n + 1 = Nat.plusR 0 n + 1
```

{anchorName plusR_succ_left (module:=Examples.DependentTypes.Pitfalls)}`congrArg`のような関数や{anchorTerm appendR (module:=Examples.DependentTypes.Pitfalls)}`▸`のような演算子に頼る代わりに、等式の証明を使ってゴールを変換するタクティクがある。
最も重要なものの一つが{kw}`rw`で、等式の証明のリストを取り、ゴールの中で左辺を右辺で置き換える。
{anchorName plusR_ind_zero_left_6}`plusR_zero_left`では、これでほぼ正しく動く。
```anchor plusR_ind_zero_left_6
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold Nat.plusR
    rw [ih]
```
しかし、書き換えの向きが逆であった。
{anchorName others}`n`を{anchorTerm others}`Nat.plusR 0 n`で置き換えたことで、ゴールは簡単になるどころか複雑になった。
```anchorError plusR_ind_zero_left_6
unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ Nat.plusR 0 n + 1 = Nat.plusR 0 (Nat.plusR 0 n) + 1
```
{kw}`rw`の呼び出しで{anchorName plusR_zero_left_done}`ih`の前に左矢印を置くと解決する。等式の右辺を左辺で置き換えるよう指示することになる。

```anchor plusR_zero_left_done
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold Nat.plusR
    rw [←ih]
```
この書き換えで等式の両辺が同じになり、Leanが{kw}`rfl`を自分で処理する。
これで証明は完了する。

# タクティクゴルフ
%%%
tag := "tactic-golf"
%%%

ここまでは、タクティク言語の本当の価値は示されていない。
上の証明は再帰関数より短くなく、Leanの言語全体ではなくドメイン固有言語で書かれているだけである。
しかしタクティクによる証明は、より短く、簡単で、保守しやすくできる。
ゴルフではスコアが低いほどよいように、タクティクゴルフでは証明が短いほどよい。

{anchorName plusR_zero_left_golf_1}`plusR_zero_left`の帰納法の段階は、簡約タクティク{tactic}`simp`で証明できる。
{tactic}`simp`をそのまま使ってもうまくいかない。
```anchor plusR_zero_left_golf_1
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp
```
```anchorError plusR_zero_left_golf_1
`simp` made no progress
```
ただし、{tactic}`simp`には定義の集合を使わせるよう設定できる。
{kw}`rw`と同じく、その引数はリストで与える。
{tactic}`simp`に{anchorName plusR_zero_left_golf_1}`Nat.plusR`の定義を考慮させると、より単純なゴールになる。
```anchor plusR_zero_left_golf_2
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp [Nat.plusR]
```
```anchorError plusR_zero_left_golf_2
unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ n = Nat.plusR 0 n
```
とくに、ゴールが帰納法の仮定とまったく同じになっている。
簡約器は、簡単な等式を自動で証明するだけでなく、{anchorTerm others}`Nat.succ A = Nat.succ B`のようなゴールを{anchorTerm others}`A = B`に自動で置き換える。
帰納法の仮定{anchorName plusR_zero_left_golf_3}`ih`がちょうど求める型なので、{kw}`exact`タクティクでそれを使うよう指示できる。

```anchor plusR_zero_left_golf_3
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp [Nat.plusR]
    exact ih
```

ただし、{kw}`exact`の使用はやや壊れやすい。
証明を「ゴルフ」しているうちに帰納法の仮定の名前を変えると、この証明は動かなくなる。
{kw}`assumption`タクティクは、前提の*いずれか*が現在のゴールに一致すれば、そのゴールを解決する。

```anchor plusR_zero_left_golf_4
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp [Nat.plusR]
    assumption
```

この証明は、展開と明示的な書き換えを使った先ほどの証明より短くはない。
しかし、{tactic}`simp`が多くの種類のゴールを解けることを活かせば、一連の変形でずっと短くできる。
まず、{kw}`induction`の末尾の{kw}`with`を外す。
構造化されて読みやすい証明には{kw}`with`の構文が便利である。
場合が足りなければ文句を言い、帰納法の構造もはっきり見える。
しかし証明を短くするには、もっと自由な書き方が要ることが多い。

{kw}`with`なしで{kw}`induction`を使うと、単にゴールが二つある証明状態になる。
{kw}`case`タクティクでその一方を選べる。{kw}`induction`{lit}` ...`{kw}`with`タクティクの枝と同じである。
言い換えれば、次の証明は先ほどの証明と等価である。

```anchor plusR_zero_left_golf_5
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k
  case zero => rfl
  case succ n ih =>
    simp [Nat.plusR]
    assumption
```

ゴールが一つだけの状況（つまり{anchorTerm plusR_zero_left_golf_6a}`k = Nat.plusR 0 k`）で、{anchorTerm plusR_zero_left_golf_5}`induction k`タクティクは二つのゴールを生む。
一般に、タクティクはエラーで失敗するか、ゴールを取り、それを0個以上の新しいゴールに変換する。
新しいゴールはそれぞれ、残っている証明すべきことを表す。
結果が0個のゴールなら、そのタクティクは成功であり、証明のその部分は終わったことになる。

{kw}`<;>`演算子は二つのタクティクを引数に取り、新しいタクティクを作る。
{lit}`T1 `{kw}`<;>`{lit}` T2`は、{lit}`T1`を現在のゴールに適用し、次に{lit}`T1`が作った*すべての*ゴールに{lit}`T2`を適用する。
言い換えれば、{kw}`<;>`を使うと、多くの種類のゴールを解ける一般的なタクティクを、複数の新しいゴールに一度に適用できる。
そのような一般的なタクティクの一つが{tactic}`simp`である。

{tactic}`simp`は基底ケースの証明を完了させ、帰納法の段階の証明も進められるので、{kw}`induction`と{kw}`<;>`と組み合わせると証明が短くなる。
```anchor plusR_zero_left_golf_6a
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k <;> simp [Nat.plusR]
```
するとゴールは一つだけになり、それは変形された帰納法の段階である。
```anchorError plusR_zero_left_golf_6a
unsolved goals
case succ
n✝ : Nat
a✝ : n✝ = Nat.plusR 0 n✝
⊢ n✝ = Nat.plusR 0 n✝
```
このゴールで{kw}`assumption`を実行すると証明が完了する。

```anchor plusR_zero_left_golf_6
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k <;> simp [Nat.plusR] <;> assumption
```
ここでは{lit}`ih`に明示的に名前を付けていないので、{kw}`exact`は使えない。

初心者にとっては、この証明は読みやすいとは言えない。
しかし熟練者によくある書き方は、{tactic}`simp`のような強力なタクティクで簡単な場合をまとめて片付け、証明の記述を面白い場合に集中させるものである。
さらに、こうした証明は、関係する関数やデータ型の小さな変更に対して壊れにくい傾向がある。
タクティクゴルフは、証明を書くときの良い感覚とスタイルを身につける上で役に立つ。

# 他のデータ型についての帰納法
%%%
tag := "induction-other-types"
%%%

数学的帰納法は、{anchorName others}`Nat.zero`の場合の基底ケースと、{anchorName others}`Nat.succ`の場合の帰納法の段階を与えることで、自然数についての主張を証明する。
帰納法の原理は他のデータ型でも成り立つ。
再帰的な引数を持たないコンストラクタが基底ケースになり、再帰的な引数を持つコンストラクタが帰納法の段階になる。
帰納法で証明できることが、これらのデータ型が*帰納的*データ型と呼ばれる理由そのものである。

その一例が二分木についての帰納法である。
二分木についての帰納法は、*すべての*二分木について主張を証明する技法で、二つの段階から成る。
 1. {anchorName TreeCtors}`BinTree.leaf`について主張が成り立つことを示す。これを基底ケースと呼ぶ。
 2. 任意に選んだ木{anchorName TreeCtors}`l`と{anchorName TreeCtors}`r`について主張が成り立つと仮定したうえで、{anchorTerm TreeCtors}`BinTree.branch l x r`（{anchorName TreeCtors}`x`は任意に選んだ新しいデータ）について成り立つことを示す。これを*帰納法の段階*と呼ぶ。{anchorName TreeCtors}`l`と{anchorName TreeCtors}`r`について主張が成り立つという仮定を*帰納法の仮定*と呼ぶ。

{anchorName BinTree_count}`BinTree.count`は木の枝の数を数える。

```anchor BinTree_count
def BinTree.count : BinTree α → Nat
  | .leaf => 0
  | .branch l _ r =>
    1 + l.count + r.count
```
{ref "leading-dot-notation"}[木を鏡映しにしても]、その木の枝の数は変わらない。
これは木についての帰納法で証明できる。
まず定理を述べ、{kw}`induction`を呼び出す。
```anchor mirror_count_0a
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => skip
  | branch l x r ihl ihr => skip
```
基底ケースは、葉を鏡映しにしたものを数えるのは、葉を数えるのと同じである、と述べている。
```anchorError mirror_count_0a
unsolved goals
case leaf
α : Type
⊢ leaf.mirror.count = leaf.count
```
帰納法の段階では、左と右の部分木を鏡映しにしてもそれぞれの枝の数は変わらないと仮定でき、それらの部分木を持つ枝を鏡映しにしても全体の枝の数が保たれることの証明を求めている。
```anchorError mirror_count_0b
unsolved goals
case branch
α : Type
l : BinTree α
x : α
r : BinTree α
ihl : l.mirror.count = l.count
ihr : r.mirror.count = r.count
⊢ (l.branch x r).mirror.count = (l.branch x r).count
```


{anchorName mirror_count_1}`leaf`を鏡映しにすると{anchorName mirror_count_1}`leaf`になるので、左辺と右辺は定義上等しく、基底ケースは成り立つ。
これは{anchorName mirror_count_1}`BinTree.mirror`を展開するよう指示した{tactic}`simp`で表せる。
```anchor mirror_count_1
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr => skip
```
帰納法の段階では、ゴールの中に帰納法の仮定とすぐに一致するものはない。
{anchorName mirror_count_2}`BinTree.count`と{anchorName mirror_count_2}`BinTree.mirror`の定義を使って簡約すると、関係が見えてくる。
```anchor mirror_count_2
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp [BinTree.mirror, BinTree.count]
```
```anchorError mirror_count_2
unsolved goals
case branch
α : Type
l : BinTree α
x : α
r : BinTree α
ihl : l.mirror.count = l.count
ihr : r.mirror.count = r.count
⊢ 1 + r.mirror.count + l.mirror.count = 1 + l.count + r.count
```
二つの帰納法の仮定を使うと、ゴールの左辺を右辺とほぼ同じ形に書き換えられる。
```anchor mirror_count_3
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp [BinTree.mirror, BinTree.count]
    rw [ihl, ihr]
```
```anchorError mirror_count_3
unsolved goals
case branch
α : Type
l : BinTree α
x : α
r : BinTree α
ihl : l.mirror.count = l.count
ihr : r.mirror.count = r.count
⊢ 1 + r.count + l.count = 1 + l.count + r.count
```

{tactic}`simp`タクティクは、{anchorTerm mirror_count_4}`+arith`オプションを渡すと、算術に関する追加の等式も使える。
これだけでこのゴールを証明でき、次のようになる。

```anchor mirror_count_4
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp [BinTree.mirror, BinTree.count]
    rw [ihl, ihr]
    simp +arith
```

簡約器には、展開する定義だけでなく、ゴールを簡約する際の書き換えに使う等式の証明の名前も渡せる。
{anchorName mirror_count_5}`BinTree.mirror_count`は次のようにも書ける。

```anchor mirror_count_5
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp +arith [BinTree.mirror, BinTree.count, ihl, ihr]
```
証明が複雑になるにつれ、前提を手で列挙するのは面倒になる。
さらに、前提の名前を手で書くと、証明の手順を複数のサブゴールで再利用しにくくなる。
{tactic}`simp`や{kw}`simp +arith`に{lit}`*`という引数を渡すと、ゴールを簡約・解決する際に*すべての*前提を使うよう指示できる。
言い換えれば、証明は次のようにも書ける。

```anchor mirror_count_6
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp +arith [BinTree.mirror, BinTree.count, *]
```
どちらの枝も簡約器を使っているので、証明は次のように短くできる。

```anchor mirror_count_7
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t <;> simp +arith [BinTree.mirror, BinTree.count, *]
```

# {lit}`grind`タクティク
%%%
tag := "grind"
%%%

{tactic}`grind`タクティクは多くの定理を自動で証明できる。
{tactic}`simp`と同じく、考慮に入れる追加の事実や展開する関数のリストを省略可能な引数として受け取る。{tactic}`simp`と違い、ローカルの前提は自動で考慮する。
さらに、{tactic}`grind`の特定の数学領域についての推論の支援は、{tactic}`simp`の算術の支援よりずっと強力である。
{anchorName mirror_count_8}`BinTree.mirror_count`の証明は、{tactic}`grind`を使う形に書き直せる。
```anchor mirror_count_8
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t <;> grind [BinTree.mirror, BinTree.count]
```

本書の証明はどれも小規模なので、ほとんどは{tactic}`grind`の力を見せる場面にはならない。
ただし、本書の後半のいくつかの証明では非常に便利である。

# 練習問題
%%%
tag := "tactics-induction-proofs-exercises"
%%%

 * {kw}`induction`{lit}` ...`{kw}`with`タクティクを使って{anchorName plusR_succ_left (module:=Examples.DependentTypes.Pitfalls)}`plusR_succ_left`を証明せよ。
 * {anchorName plusR_succ_left (module:=Examples.DependentTypes.Pitfalls)}`plusR_succ_left`の証明を、{kw}`<;>`を使って1行に書き直せ。
 * リストについての帰納法を使って、リストの連結が結合法則を満たすことを証明せよ。
   ```anchorTerm ex
   theorem List.append_assoc (xs ys zs : List α) :
       xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
   ```
