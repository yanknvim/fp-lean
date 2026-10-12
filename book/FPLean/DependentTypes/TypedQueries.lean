module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.DependentTypes.DB"

#doc (Manual) "Worked Example: Typed Queries" =>
%%%
tag := "typed-queries"
%%%

添字付き族は、他の言語に似せたAPIを作るときに非常に役に立つ。
不正なHTMLを生成できないHTMLコンストラクタのライブラリを書いたり、設定ファイルの形式の細かな規則を符号化したり、複雑な業務上の制約をモデル化したりするのに使える。
この節では、より強力なデータベース問い合わせ言語を作るのに使える技法の、より単純な実演として、関係代数の部分集合を添字付き族を使ってLeanで符号化する方法を述べる。

この部分集合は、フィールド名が重ならないことなどの要件を型システムで強制し、型の段階の計算を使ってスキーマを問い合わせが返す値の型に反映する。
しかし現実的な仕組みではない。データベースは連結リストの連結リストで表され、型システムはSQLのものよりずっと単純であり、関係代数の演算子はSQLのものとはあまり一致しない。
しかし、役に立つ原理と技法を示すには十分な大きさである。

# データの宇宙
%%%
tag := "typed-query-data-universe"
%%%

この関係代数では、列に入れられる基本のデータは{anchorName DBType}`Int`、{anchorName DBType}`String`、{anchorName DBType}`Bool`の型を持ち、宇宙{anchorName DBType}`DBType`で記述される。

```anchor DBType
inductive DBType where
  | int | string | bool

abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
```

{anchorName DBType}`DBType.asType`を使うと、これらのコードを型として使える。
たとえば、
```anchor mountHoodEval
#eval ("Mount Hood" : DBType.string.asType)
```
```anchorInfo mountHoodEval
"Mount Hood"
```

三つのデータベースの型が記述する値は、どれも等しさを比べられる。
しかし、これをLeanに説明するには少し手間が要る。
単に{anchorName BEqDBType}`BEq`を直接使うとうまくいかない。
```anchor dbEqNoSplit
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  x == y
```
```anchorError dbEqNoSplit
failed to synthesize instance of type class
  BEq t.asType

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
入れ子の組の宇宙と同じく、型クラスの探索は{anchorName dbEqNoSplit}`t`の値の起こりうる場合を自動で調べない。
解決策は、パターンマッチングで{anchorTerm dbEq}`x`と{anchorName dbEq}`y`の型を洗練することである。

```anchor dbEq
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
```
この版の関数では、三つの場合でそれぞれ{anchorName dbEq}`x`と{anchorName dbEq}`y`の型が{anchorName DBType}`Int`、{anchorName DBType}`String`、{anchorName DBType}`Bool`になり、これらの型にはすべて{anchorName BEqDBType}`BEq`インスタンスがある。
{anchorName dbEq}`DBType.beq`の定義を使うと、{anchorName DBType}`DBType`がコード化する型の{anchorName BEqDBType}`BEq`インスタンスを定義できる。

```anchor BEqDBType
instance {t : DBType} : BEq t.asType where
  beq := t.beq
```
これはコード自体のインスタンスとは同じではない。

```anchor BEqDBTypeCodes
instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | _, _ => false
```
前者のインスタンスはコードが記述する型から取り出した値を比べられ、後者はコード自体を比べられる。

{anchorName ReprAsType}`Repr`インスタンスも同じ技法で書ける。
{anchorName ReprAsType}`Repr`クラスのメソッドが{anchorName ReprAsType}`reprPrec`と呼ばれるのは、値を表示するときに演算子の優先度のようなものを考慮するようにできているためである。
依存パターンマッチングで型を洗練すると、{anchorName DBType}`Int`、{anchorName DBType}`String`、{anchorName DBType}`Bool`の{anchorName ReprAsType}`Repr`インスタンスの{anchorName ReprAsType}`reprPrec`メソッドを使える。

```anchor ReprAsType
instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec
```

# スキーマと表
%%%
tag := "schemas"
%%%

スキーマはデータベースの各列の名前と型を記述する。

```anchor Schema
structure Column where
  name : String
  contains : DBType

abbrev Schema := List Column
```
実際、スキーマは表の行を記述する宇宙と見なせる。
空のスキーマはunit型を記述し、列が一つのスキーマはその値そのものを記述し、列が二つ以上あるスキーマはタプルで表す。

```anchor Row
abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)
```

{ref "prod"}[直積型についての最初の節]で述べたように、Leanの直積型とタプルは右結合である。
つまり、入れ子になった組は普通の平坦なタプルと等価である。

表は、スキーマを共有する行のリストである。

```anchor Table
abbrev Table (s : Schema) := List (Row s)
```
たとえば、山の頂を訪れた記録はスキーマ{anchorName peak}`peak`で表せる。

```anchor peak
abbrev peak : Schema := [
  ⟨"name", .string⟩,
  ⟨"location", .string⟩,
  ⟨"elevation", .int⟩,
  ⟨"lastVisited", .int⟩
]
```
この本の著者が訪れた山の頂の抜粋は、普通のタプルのリストとして現れる。

```anchor mountainDiary
def mountainDiary : Table peak := [
  ("Mount Nebo",       "USA",     3637, 2013),
  ("Moscow Mountain",  "USA",     1519, 2015),
  ("Himmelbjerget",    "Denmark",  147, 2004),
  ("Mount St. Helens", "USA",     2549, 2010)
]
```
もう一つの例は滝と、それを訪れた記録から成る。

```anchor waterfall
abbrev waterfall : Schema := [
  ⟨"name", .string⟩,
  ⟨"location", .string⟩,
  ⟨"lastVisited", .int⟩
]
```

```anchor waterfallDiary
def waterfallDiary : Table waterfall := [
  ("Multnomah Falls", "USA", 2018),
  ("Shoshone Falls",  "USA", 2014)
]
```

## 再帰と宇宙、再訪
%%%
tag := "recursion-universes-revisited"
%%%

行をタプルとして便利に構造化することには代償がある。{anchorName Row}`Row`が二つの基底の場合を別々に扱うということは、{anchorName Row}`Row`を型に使い、コード（つまりスキーマ）について再帰的に定義される関数も、同じ区別をせねばならないということである。
これが問題になる例の一つは、スキーマについての再帰を使って行の等しさを調べる関数を定義する等価性の検査である。
この例はLeanの型検査器を通らない。
```anchor RowBEqRecursion
def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | col::cols =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'
```
```anchorError RowBEqRecursion
Type mismatch
  (v1, r1')
has type
  ?m.10 × ?m.11
but is expected to have type
  Row (col :: cols)
```
問題は、パターン{anchorTerm RowBEqRecursion}`col :: cols`が行の型を十分に洗練しないことである。
{anchorName Row}`Row`の定義で、単一要素のパターン{anchorTerm Row}`[col]`と{anchorTerm Row}`col1 :: col2 :: cols`のどちらにマッチしたかをLeanがまだ判断できず、{anchorName Row}`Row`の呼び出しが組の型まで計算されないためである。
解決策は、{anchorName RowBEq}`Row.bEq`の定義で{anchorName Row}`Row`の構造を写すことである。

```anchor RowBEq
def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _::_::_ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'

instance : BEq (Row s) where
  beq := Row.bEq
```

他の文脈と違い、型に現れる関数は、その入力と出力の振る舞いだけで考えることはできない。
これらの型を使うプログラムは、その構造が型のパターンマッチングと再帰の振る舞いに一致するように、型の段階の関数で使った算法を写すことを強いられる。
依存型を使ったプログラミングの技能の大きな部分は、正しい計算の振る舞いを持つ適切な型の段階の関数を選ぶことである。

## 列へのポインタ
%%%
tag := "column-pointers"
%%%

スキーマがある列を含むときにだけ意味をなす問い合わせもある。
たとえば、標高が1000メートルより高い山を返す問い合わせは、整数を入れる{anchorTerm peak}`"elevation"`列を持つスキーマの文脈でだけ意味をなす。
ある列がスキーマに含まれることを示す一つの方法は、その列へのポインタを直接与えることであり、そのポインタを添字付き族として定義すれば、不正なポインタを排除できる。

列がスキーマにある方法は二通りある。スキーマの先頭にあるか、スキーマのもっと後にあるかである。
列がスキーマの後ろにあるなら、結局はスキーマのある残りの先頭になる。

添字付き族{anchorName HasCol}`HasCol`は、その仕様をLeanのコードに移したものである。

```anchor HasCol
inductive HasCol : Schema → String → DBType → Type where
  | here : HasCol (⟨name, t⟩ :: _) name t
  | there : HasCol s name t → HasCol (_ :: s) name t
```
この族の三つの引数は、スキーマ、列の名前、その型である。
三つとも添字だが、引数の順序を変えてスキーマを列の名前と型の後に置けば、名前と型をパラメータにできる。
コンストラクタ{anchorName HasCol}`here`は、スキーマが列{anchorTerm HasCol}`⟨name, t⟩`で始まるときに使える。つまりこれは、最初の列が求める名前と型を持つときにだけ使える、スキーマの最初の列へのポインタである。
コンストラクタ{anchorName HasCol}`there`は、より小さなスキーマへのポインタを、列が一つ増えたスキーマへのポインタに変換する。

{anchorTerm peak}`"elevation"`は{anchorName peak}`peak`の三番目の列なので、{anchorName HasCol}`there`で最初の二つの列を見送れば見つかり、そのあとは最初の列である。
言い換えれば、型{anchorTerm peakElevationInt}`HasCol peak "elevation" .int`を満たすには、式{anchorTerm peakElevationInt}`.there (.there .here)`を使う。
{anchorName HasCol}`HasCol`は一種の装飾された{anchorName Naturals}`Nat`と考えることもできる。{anchorName Naturals}`zero`が{anchorName HasCol}`here`に、{anchorName Naturals}`succ`が{anchorName HasCol}`there`に対応する。
余分な型の情報により、一つずれの誤りは起こりえない。

スキーマの特定の列へのポインタを使うと、行からその列の値を取り出せる。

```anchor Rowget
def Row.get (row : Row s) (col : HasCol s n t) : t.asType :=
  match s, col, row with
  | [_], .here, v => v
  | _::_::_, .here, (v, _) => v
  | _::_::_, .there next, (_, r) => get r next
```
まずスキーマでパターンマッチングする。これで行がタプルか単一の値かが決まるためである。
空のスキーマの場合を書く必要はない。{anchorName HasCol}`HasCol`があるということ自体が、そのどちらのコンストラクタも空でないスキーマを指定していることを意味するためである。
スキーマの列が一つだけなら、ポインタはそれを指さねばならないので、{anchorName HasCol}`HasCol`の{anchorName HasCol}`here`コンストラクタだけをマッチさせればよい。
スキーマの列が二つ以上なら、{anchorName HasCol}`here`の場合（そのとき値は行の最初のもの）と、{anchorName HasCol}`there`の場合（そのとき再帰呼び出しを使う）が必要である。
{anchorName HasCol}`HasCol`型がその列が行に存在することを保証するので、{anchorName Rowget}`Row.get`は{anchorName nullable}`Option`を返す必要がない。

{anchorName HasCol}`HasCol`は二つの役割を果たす。
 1. 特定の名前と型を持つ列がスキーマに存在するという*証拠*として働く。

 2. 行の中でその列に対応する値を見つけるのに使える*データ*として働く。

一つ目の役割、つまり証拠としての役割は、命題の使われ方に似ている。
添字付き族{anchorName HasCol}`HasCol`の定義は、ある列が存在することの証拠として何が認められるかの仕様として読める。
しかし命題と違い、{anchorName HasCol}`HasCol`のどのコンストラクタを使ったかが問題になる。
二つ目の役割では、コンストラクタが{anchorName Naturals}`Nat`のように使われ、集まりの中のデータを見つける。
添字付き族を使ったプログラミングでは、両方の観点を自在に行き来できることがしばしば必要である。

## 部分スキーマ
%%%
tag := "subschemas"
%%%

関係代数の重要な操作の一つは、表や行をより小さなスキーマへ*射影*することである。
小さなスキーマにない列はすべて忘れられる。
射影が意味をなすには、小さなスキーマが大きなスキーマの部分スキーマでなければならない。つまり、小さなスキーマのどの列も大きなスキーマに存在しなければならない。
{anchorName HasCol}`HasCol`が失敗しえない一行の一列の参照を書けるようにするのと同じく、部分スキーマの関係を添字付き族として表せば、失敗しえない射影の関数を書ける。

あるスキーマが別のスキーマの部分スキーマになりうる方法は、添字付き族として定義できる。
基本的な考え方は、小さなスキーマのどの列も大きなスキーマに現れるなら、その小さなスキーマは大きなスキーマの部分スキーマである、というものである。
小さなスキーマが空なら、それは確かに大きなスキーマの部分スキーマであり、コンストラクタ{anchorName Subschema}`nil`で表す。
小さなスキーマに列があれば、その列は大きなスキーマになければならず、部分スキーマの残りの列もすべて大きなスキーマの部分スキーマでなければならない。
これはコンストラクタ{anchorName Subschema}`cons`で表す。

```anchor Subschema
inductive Subschema : Schema → Schema → Type where
  | nil : Subschema [] bigger
  | cons :
      HasCol bigger n t →
      Subschema smaller bigger →
      Subschema (⟨n, t⟩ :: smaller) bigger
```
言い換えれば、{anchorName Subschema}`Subschema`は小さなスキーマの各列に、大きなスキーマでの位置を指す{anchorName HasCol}`HasCol`を割り当てる。

スキーマ{anchorName travelDiary}`travelDiary`は、{anchorName peak}`peak`と{anchorName waterfall}`waterfall`の両方に共通するフィールドを表す。

```anchor travelDiary
abbrev travelDiary : Schema :=
  [⟨"name", .string⟩, ⟨"location", .string⟩, ⟨"lastVisited", .int⟩]
```
次の例が示すように、これは確かに{anchorName peak}`peak`の部分スキーマである。

```anchor peakDiarySub
example : Subschema travelDiary peak :=
  .cons .here
    (.cons (.there .here)
      (.cons (.there (.there (.there .here))) .nil))
```
しかし、このようなコードは読みにくく、保守しにくい。
これをよくする一つの方法は、{anchorName Subschema}`Subschema`と{anchorName HasCol}`HasCol`のコンストラクタを自動で書くようLeanに指示することである。
これは{ref "props-proofs-indexing"}[命題と証明についての幕間]で紹介したタクティクの機能を使って行える。
その幕間では、{kw}`by decide`と{kw}`by simp`を使ってさまざまな命題の証拠を与えた。

この文脈では、二つのタクティクが役に立つ。
 * {kw}`constructor`タクティクは、データ型のコンストラクタを使って問題を解くようLeanに指示する。
 * {kw}`repeat`タクティクは、失敗するか証明が終わるまでタクティクを繰り返すようLeanに指示する。

次の例では、{kw}`by constructor`は単に{anchorName peakDiarySub}`.nil`と書くのと同じ効果がある。

```anchor emptySub
example : Subschema [] peak := by constructor
```
しかし、もう少し複雑な型で同じタクティクを試すと失敗する。
```anchor notDone
example : Subschema [⟨"location", .string⟩] peak := by constructor
```
```anchorError notDone
unsolved goals
case a
⊢ HasCol peak "location" DBType.string

case a
⊢ Subschema [] peak
```
{lit}`unsolved goals`で始まるエラーは、本来組み立てるべき式を完全には組み立てられなかったタクティクを表す。
Leanのタクティク言語で、*ゴール*とは、タクティクが裏で適切な式を組み立てることで満たすべき型である。
この場合、{kw}`constructor`が{anchorName SubschemaNames}`Subschema.cons`を適用させ、二つのゴールが{anchorName Subschema}`cons`の期待する二つの引数を表している。
{kw}`constructor`をもう一つ加えると、{anchorName peak}`peak`の最初の列が{anchorTerm SubschemaNames}`"location"`ではないので、一つ目のゴール（{anchorTerm SubschemaNames}`HasCol peak "location" DBType.string`）が{anchorName SubschemaNames}`HasCol.there`で扱われる。
```anchor notDone2
example : Subschema [⟨"location", .string⟩] peak := by
  constructor
  constructor
```
```anchorError notDone2
unsolved goals
case a
⊢ HasCol
  [{ name := "location", contains := DBType.string }, { name := "elevation", contains := DBType.int },
    { name := "lastVisited", contains := DBType.int }]
  "location" DBType.string

case a
⊢ Subschema [] peak
```
しかし、{kw}`constructor`を三つ目に加えると、{anchorName SubschemaNames}`HasCol.here`が適用できるので、一つ目のゴールが解決される。
```anchor notDone3
example : Subschema [⟨"location", .string⟩] peak := by
  constructor
  constructor
  constructor
```
```anchorError notDone3
unsolved goals
case a
⊢ Subschema [] peak
```
{kw}`constructor`の四つ目で、{anchorTerm SubschemaNames}`Subschema peak []`のゴールが解決する。

```anchor notDone4
example : Subschema [⟨"location", .string⟩] peak := by
  constructor
  constructor
  constructor
  constructor
```
実際、タクティクを使わずに書いた版ではコンストラクタが四つある。

```anchor notDone5
example : Subschema [⟨"location", .string⟩] peak :=
  .cons (.there .here) .nil
```

{kw}`constructor`を何回書けばよいか試行錯誤する代わりに、{kw}`repeat`タクティクを使って、進展がある限り{kw}`constructor`を試し続けるようLeanに頼める。

```anchor notDone6
example : Subschema [⟨"location", .string⟩] peak := by repeat constructor
```
このより柔軟な版は、より興味深い{anchorName Subschema}`Subschema`の問題でも働く。

```anchor subschemata
example : Subschema travelDiary peak := by repeat constructor

example : Subschema travelDiary waterfall := by repeat constructor
```

何かが通るまでやみくもにコンストラクタを試すやり方は、{anchorName Naturals}`Nat`や{anchorTerm misc}`List Bool`のような型にはあまり役に立たない。
何しろ、式が{anchorName Naturals}`Nat`型を持つからといって、それが*正しい*{anchorName Naturals}`Nat`であるとは限らない。
しかし{anchorName HasCol}`HasCol`や{anchorName Subschema}`Subschema`のような型は、添字によって十分に制約されているので、適用できるコンストラクタは常に一つだけであり、つまりプログラムの中身自体の面白みは薄く、コンピュータが正しいものを選べる。

あるスキーマが別のスキーマの部分スキーマなら、列を一つ加えて拡張した大きなスキーマの部分スキーマでもある。
この事実は関数の定義としてとらえられる。
{anchorName SubschemaAdd}`Subschema.addColumn`は、{anchorName SubschemaAdd}`smaller`が{anchorName SubschemaAdd}`bigger`の部分スキーマである証拠を取り、{anchorName SubschemaAdd}`smaller`が{anchorTerm SubschemaAdd}`c :: bigger`、つまり列を一つ加えた{anchorName SubschemaAdd}`bigger`の部分スキーマである証拠を返す。

```anchor SubschemaAdd
def Subschema.addColumn :
    Subschema smaller bigger →
    Subschema smaller (c :: bigger)
  | .nil  => .nil
  | .cons col sub' => .cons (.there col) sub'.addColumn
```
部分スキーマは、小さなスキーマの各列を大きなスキーマのどこに見つけるかを記述する。
{anchorName SubschemaAdd}`Subschema.addColumn`は、これらの記述を元の大きなスキーマから拡張した大きなスキーマへ移さねばならない。
{anchorName Subschema}`nil`の場合は、小さなスキーマは{lit}`[]`であり、{anchorName Subschema}`nil`は{lit}`[]`が{anchorTerm SubschemaAdd}`c :: bigger`の部分スキーマである証拠でもある。
{anchorName Subschema}`cons`の場合は、{anchorName SubschemaAdd}`smaller`の一つの列を{anchorName SubschemaAdd}`bigger`にどう置くかを記述しており、新しい列{anchorName SubschemaAdd}`c`を考慮してその列の位置を{anchorName HasCol}`there`で調整する必要があり、再帰呼び出しが残りの列を調整する。

{anchorName Subschema}`Subschema`のもう一つの見方は、二つのスキーマの間の*関係*を定義しているというものである。型{anchorTerm misc}`Subschema smaller bigger`の式が存在することは、{anchorTerm misc}`(smaller, bigger)`がその関係にあることを意味する。
この関係は反射的であり、つまりどのスキーマもそれ自身の部分スキーマである。

```anchor SubschemaSame
def Subschema.reflexive : (s : Schema) → Subschema s s
  | [] => .nil
  | _ :: cs => .cons .here (reflexive cs).addColumn
```


## 行の射影
%%%
tag := "projecting-rows"
%%%

{anchorName RowProj}`s'`が{anchorName RowProj}`s`の部分スキーマである証拠があれば、{anchorName RowProj}`s`の行を{anchorName RowProj}`s'`の行へ射影できる。
これは、{anchorName RowProj}`s'`が{anchorName RowProj}`s`の部分スキーマである証拠を使って行う。その証拠が、{anchorName RowProj}`s'`の各列を{anchorName RowProj}`s`のどこに見つけるかを説明する。
{anchorName RowProj}`s'`の新しい行は、古い行の適切な場所から値を取り出して一列ずつ組み立てられる。

この射影を行う{anchorName RowProj}`Row.project`関数には三つの場合があり、{anchorName RowProj}`Row`自体の各場合に対応する。
射影した行を組み立てるのに、{anchorName Rowget}`Row.get`を{anchorName RowProj}`Subschema`引数の各{anchorName HasCol}`HasCol`とともに使う。

```anchor RowProj
def Row.project (row : Row s) : (s' : Schema) → Subschema s' s → Row s'
  | [], .nil => ()
  | [_], .cons c .nil => row.get c
  | _::_::_, .cons c cs => (row.get c, row.project _ cs)
```


# 条件と選択
%%%
tag := "conditions-and-selection"
%%%

射影は表から不要な列を取り除くが、問い合わせは不要な行も取り除けねばならない。
この操作を*選択*と呼ぶ。
選択は、どの行が望ましいかを表す手段があって初めて成り立つ。

この例の問い合わせ言語には式があり、SQLの{lit}`WHERE`句に書けるものに相当する。
式は添字付き族{anchorName DBExpr}`DBExpr`で表す。
式はデータベースの列を参照できるが、異なる部分式はすべて同じスキーマを持つので、{anchorName DBExpr}`DBExpr`はデータベースのスキーマをパラメータに取る。
さらに、各式には型があり、それは変化するので添字になる。

```anchor DBExpr
inductive DBExpr (s : Schema) : DBType → Type where
  | col (n : String) (loc : HasCol s n t) : DBExpr s t
  | eq (e1 e2 : DBExpr s t) : DBExpr s .bool
  | lt (e1 e2 : DBExpr s .int) : DBExpr s .bool
  | and (e1 e2 : DBExpr s .bool) : DBExpr s .bool
  | const : t.asType → DBExpr s t
```
{anchorName DBExpr}`col`コンストラクタは、データベースの列への参照を表す。
{anchorName DBExpr}`eq`コンストラクタは二つの式の等しさを比べ、{anchorName DBExpr}`lt`は一方が他方より小さいかを調べ、{anchorName DBExpr}`and`は真偽値の連言、{anchorName DBExpr}`const`はある型の定数値である。

たとえば、{anchorName peak}`peak`において、{lit}`elevation`列が1000より大きく、場所が{anchorTerm mountainDiary}`"Denmark"`かを調べる式は次のように書ける。

```anchor tallDk
def tallInDenmark : DBExpr peak .bool :=
  .and (.lt (.const 1000) (.col "elevation" (by repeat constructor)))
       (.eq (.col "location" (by repeat constructor)) (.const "Denmark"))
```
これは少し煩わしい。
特に、列への参照に{anchorTerm tallDk}`by repeat constructor`の定型の呼び出しが含まれる。
*マクロ*と呼ばれるLeanの機能を使うと、この定型を取り除いて式を読みやすくできる。

```anchor cBang
macro "c!" n:term : term => `(DBExpr.col $n (by repeat constructor))
```
この宣言は{kw}`c!`キーワードをLeanに加え、{kw}`c!`の後に式が続く箇所を、対応する{anchorTerm cBang}`DBExpr.col`の構成に置き換えるようLeanに指示する。
ここで{anchorName cBang}`term`は、コマンドやタクティク、その他の言語の部分ではなく、Leanの式を表す。
LeanのマクロはCのプリプロセッサのマクロに少し似ているが、言語によりよく統合されており、CPPの落とし穴のいくつかを自動で避ける。
実際、SchemeやRacketのマクロと非常に密接に関係している。

このマクロを使うと、式はずっと読みやすくなる。

```anchor tallDkBetter
def tallInDenmark : DBExpr peak .bool :=
  .and (.lt (.const 1000) (c! "elevation"))
       (.eq (c! "location") (.const "Denmark"))
```

与えられた行について式の値を求めるには、列への参照を取り出すのに{anchorName Rowget}`Row.get`を使い、それ以外の式については値に対するLeanの操作に委ねる。

```anchor DBExprEval
def DBExpr.evaluate (row : Row s) : DBExpr s t → t.asType
  | .col _ loc => row.get loc
  | .eq e1 e2  => evaluate row e1 == evaluate row e2
  | .lt e1 e2  => evaluate row e1 < evaluate row e2
  | .and e1 e2 => evaluate row e1 && evaluate row e2
  | .const v => v
```

コペンハーゲン周辺で最も高い丘であるヴァルビュ・バッケについてこの式を評価すると{anchorName misc}`false`になる。ヴァルビュ・バッケは海面から1kmよりずっと低いためである。
```anchor valbybakke
#eval tallInDenmark.evaluate ("Valby Bakke", "Denmark", 31, 2023)
```
```anchorInfo valbybakke
false
```
標高1230mの架空の山について評価すると{anchorName misc}`true`になる。
```anchor fakeDkBjerg
#eval tallInDenmark.evaluate ("Fictional mountain", "Denmark", 1230, 2023)
```
```anchorInfo fakeDkBjerg
true
```
アメリカのアイダホ州で最も高い山について評価すると{anchorName misc}`false`になる。アイダホはデンマークの一部ではないためである。
```anchor borah
#eval tallInDenmark.evaluate ("Mount Borah", "USA", 3859, 1996)
```
```anchorInfo borah
false
```

# 問い合わせ
%%%
tag := "typed-query-language"
%%%

この問い合わせ言語は関係代数に基づいている。
表に加えて、次の演算子がある。
 1. 同じスキーマを持つ二つの式の和は、二つの問い合わせから生じる行を合わせる。
 2. 同じスキーマを持つ二つの式の差は、一つ目の結果の行から、二つ目の結果にある行を取り除く。
 3. ある基準による選択は、式に従って問い合わせの結果を絞り込む。
 4. 部分スキーマへの射影は、問い合わせの結果から列を取り除く。
 5. 直積は、一方の問い合わせのどの行も他方の問い合わせのどの行とも組み合わせる。
 6. 問い合わせの結果の列の名前を変える。これはスキーマを変更する。
 7. 問い合わせのすべての列の名前に接頭辞を付ける。

最後の演算子は必ずしも必要ではないが、言語を使いやすくする。

ここでもまた、問い合わせは添字付き族で表す。

```anchor Query
inductive Query : Schema → Type where
  | table : Table s → Query s
  | union : Query s → Query s → Query s
  | diff : Query s → Query s → Query s
  | select : Query s → DBExpr s .bool → Query s
  | project :
    Query s → (s' : Schema) →
    Subschema s' s →
    Query s'
  | product :
    Query s1 → Query s2 →
    disjoint (s1.map Column.name) (s2.map Column.name) →
    Query (s1 ++ s2)
  | renameColumn :
    Query s → (c : HasCol s n t) → (n' : String) →
    !((s.map Column.name).contains n') →
    Query (s.renameColumn c n')
  | prefixWith :
    (n : String) → Query s →
    Query (s.map fun c => {c with name := n ++ "." ++ c.name})
```
{anchorName Query}`select`コンストラクタは、選択に使う式が真偽値を返すことを要求する。
{anchorName Query}`product`コンストラクタの型には{anchorName Query}`disjoint`の呼び出しが含まれ、二つのスキーマが名前を共有しないことを保証する。

```anchor disjoint
def disjoint [BEq α] (xs ys : List α) : Bool :=
  not (xs.any ys.contains || ys.any xs.contains)
```
型が期待される場所で{anchorName misc}`Bool`型の式を使うと、{anchorName misc}`Bool`から{anchorTerm misc}`Prop`への型強制が働く。
決定可能な命題を真偽値と見なし、その命題の証拠が{anchorName misc}`true`に、その命題の反証が{anchorName misc}`false`に型強制できるのと同じように、真偽値は、その式が{anchorName misc}`true`に等しいという命題に型強制される。
このライブラリの使用はすべて、スキーマが事前に分かっている文脈で起きることが想定されているので、この命題は{kw}`by simp`で証明できる。
同様に、{anchorName renameColumn}`renameColumn`コンストラクタは、新しい名前がスキーマにすでに存在しないことを調べる。
{anchorName HasCol}`HasCol`が指す列の名前を変えるのに、補助関数{anchorName renameColumn}`Schema.renameColumn`を使う。

```anchor renameColumn
def Schema.renameColumn : (s : Schema) → HasCol s n t → String → Schema
  | c :: cs, .here, n' => {c with name := n'} :: cs
  | c :: cs, .there next, n' => c :: renameColumn cs next n'
```

# 問い合わせの実行
%%%
tag := "executing-queries"
%%%

問い合わせの実行にはいくつかの補助関数が要る。
問い合わせの結果は表である。つまり、問い合わせ言語の各操作には、表を扱う対応する実装が必要である。

## 直積
%%%
tag := "executing-cartesian-product"
%%%

二つの表の直積は、一つ目の表の各行を二つ目の表の各行に付けることで取る。
まず、{anchorName Row}`Row`の構造のため、行に列を一つ加えるには、結果が裸の値になるかタプルになるかを決めるのにそのスキーマでパターンマッチングする必要がある。
これはよくある操作なので、パターンマッチングを補助関数としてくくり出すと便利である。

```anchor addVal
def addVal (v : c.contains.asType) (row : Row s) : Row (c :: s) :=
  match s, row with
  | [], () => v
  | c' :: cs, v' => (v, v')
```
二つの行を付けるのは、一つ目のスキーマと一つ目の行の両方の構造について再帰的である。行の構造はスキーマの構造と歩調を合わせて進むためである。
一つ目の行が空なら、付け足しは二つ目の行を返す。
一つ目の行が単一の値なら、その値が二つ目の行に加えられる。
一つ目の行が複数の列を含むなら、最初の列の値が、その行の残りについての再帰の結果に加えられる。

```anchor RowAppend
def Row.append (r1 : Row s1) (r2 : Row s2) : Row (s1 ++ s2) :=
  match s1, r1 with
  | [], () => r2
  | [_], v => addVal v r2
  | _::_::_, (v, r') => (v, r'.append r2)
```

標準ライブラリにある{anchorName ListFlatMap}`List.flatMap`は、それ自体がリストを返す関数を入力のリストの各要素に適用し、得られたリストを順に付けた結果を返す。

```anchor ListFlatMap
def List.flatMap (f : α → List β) : (xs : List α) → List β
  | [] => []
  | x :: xs => f x ++ xs.flatMap f
```
この型シグネチャは、{anchorName ListFlatMap}`List.flatMap`が{anchorTerm ListMonad}`Monad List`インスタンスの実装に使えることを示唆している。
実際、{anchorTerm ListMonad}`pure x := [x]`と合わせれば、{anchorName ListFlatMap}`List.flatMap`はモナドを実装する。
しかし、あまり役に立つ{anchorName ListMonad}`Monad`インスタンスではない。
{anchorName ListMonad}`List`モナドは基本的に、利用者がいくつかの値を要求する機会を得る前に、探索空間の*あらゆる*可能な道筋を前もってたどる{anchorName Many (module:=Examples.Monads.Many)}`Many`の版である。
この性能のわなのため、{anchorName ListMonad}`List`の{anchorName ListMonad}`Monad`インスタンスを定義するのは普通はよくない。
しかしここでは、この問い合わせ言語には返す結果の数を制限する演算子がないので、すべての可能性を組み合わせることがまさに望ましい。

```anchor TableCartProd
def Table.cartesianProduct (table1 : Table s1) (table2 : Table s2) :
    Table (s1 ++ s2) :=
  table1.flatMap fun r1 => table2.map r1.append
```

{anchorName ListProduct (module:=Examples.DependentTypes.Finite)}`List.product`と同じく、恒等モナドでの変更を伴うループを別の実装技法として使える。

```anchor TableCartProdOther
def Table.cartesianProduct (table1 : Table s1) (table2 : Table s2) :
    Table (s1 ++ s2) := Id.run do
  let mut out : Table (s1 ++ s2) := []
  for r1 in table1 do
    for r2 in table2 do
      out := (r1.append r2) :: out
  pure out.reverse
```


## 差
%%%
tag := "executing-difference"
%%%

表から不要な行を取り除くには{anchorName misc}`List.filter`を使える。これはリストと、{anchorName misc}`Bool`を返す関数を取る。
その関数が{anchorName misc}`true`を返す要素だけを含む新しいリストが返る。
たとえば、
```anchorTerm filterA
["Willamette", "Columbia", "Sandy", "Deschutes"].filter (·.length > 8)
```
は次のように評価される。
```anchorTerm filterA
["Willamette", "Deschutes"]
```
{anchorTerm filterA}`"Columbia"`と{anchorTerm filterA}`"Sandy"`の長さが{anchorTerm filterA}`8`以下だからである。
表の要素を取り除くには、補助関数{anchorName ListWithout}`List.without`を使える。

```anchor ListWithout
def List.without [BEq α] (source banned : List α) : List α :=
  source.filter fun r => !(banned.contains r)
```
これは問い合わせを解釈するときに、{anchorName Row}`Row`の{anchorName BEqDBType}`BEq`インスタンスとともに使う。

## 列の名前の変更
%%%
tag := "executing-renaming-columns"
%%%
行の列の名前を変えるには、問題の列が見つかるまで行をたどる再帰関数を使う。見つかったところで、新しい名前の列が古い名前の列と同じ値を得る。

```anchor renameRow
def Row.rename (c : HasCol s n t) (row : Row s) :
    Row (s.renameColumn c n') :=
  match s, row, c with
  | [_], v, .here => v
  | _::_::_, (v, r), .here => (v, r)
  | _::_::_, (v, r), .there next => addVal v (r.rename next)
```
この関数は引数の*型*を変えるが、実際に返る値は元の引数とまったく同じデータを含む。
実行時の観点では、{anchorName renameRow}`Row.rename`は遅い恒等関数にすぎない。
添字付き族を使ったプログラミングの難しさの一つは、性能が問題になるときに、この種の操作が妨げになることである。
この種の「添字の付け替え」関数をなくすには、非常に注意深く、しばしば壊れやすい設計が要る。

## 列の名前への接頭辞の付加
%%%
tag := "executing-prefixing-column-names"
%%%

列の名前に接頭辞を加えるのは、列の名前を変えるのとよく似ている。
目的の列まで進んでから返るのではなく、{anchorName prefixRow}`prefixRow`はすべての列を処理せねばならない。

```anchor prefixRow
def prefixRow (row : Row s) :
    Row (s.map fun c => {c with name := n ++ "." ++ c.name}) :=
  match s, row with
  | [], _ => ()
  | [_], v => v
  | _::_::_, (v, r) => (v, prefixRow r)
```
これは、表のすべての行に接頭辞を加えるのに{anchorName misc}`List.map`とともに使える。
ここでもまた、この関数は値の型を変えるためだけに存在する。

## 部品を組み合わせる
%%%
tag := "query-exec-runner"
%%%

これらの補助関数をすべて定義すれば、問い合わせの実行には短い再帰関数だけで足りる。

```anchor QueryExec
def Query.exec : Query s → Table s
  | .table t => t
  | .union q1 q2 => exec q1 ++ exec q2
  | .diff q1 q2 => exec q1 |>.without (exec q2)
  | .select q e => exec q |>.filter e.evaluate
  | .project q _ sub => exec q |>.map (·.project _ sub)
  | .product q1 q2 _ => exec q1 |>.cartesianProduct (exec q2)
  | .renameColumn q c _ _ => exec q |>.map (·.rename c)
  | .prefixWith _ q => exec q |>.map prefixRow
```
コンストラクタのいくつかの引数は実行中に使われない。
特に、コンストラクタ{anchorName Query}`project`と関数{anchorName RowProj}`Row.project`はどちらも小さなスキーマを明示的な引数に取るが、そのスキーマが大きなスキーマの部分スキーマであるという*証拠*の型に、Leanが引数を自動で埋めるのに十分な情報が含まれている。
同様に、{anchorName Query}`product`コンストラクタが要求する、二つの表の列の名前が重ならないという事実は、{anchorName TableCartProd}`Table.cartesianProduct`には要らない。
一般に、依存型はLeanにプログラマの代わりに引数を埋めてもらう機会を多く与える。

問い合わせの結果に対してドット記法を使い、{lit}`Table`と{lit}`List`の両方の名前空間で定義された関数、たとえば{anchorName misc}`List.map`、{anchorName misc}`List.filter`、{anchorName TableCartProd}`Table.cartesianProduct`を呼び出している。
これが働くのは、{anchorName Table}`Table`が{kw}`abbrev`で定義されているためである。
型クラスの探索と同じく、ドット記法は{kw}`abbrev`で作られた定義を見通せる。

{anchorName Query}`select`の実装もかなり簡潔である。
問い合わせ{anchorName selectCase}`q`を実行した後、式を満たさない行を取り除くのに{anchorName misc}`List.filter`を使う。
{anchorName misc}`List.filter`は{anchorTerm Table}`Row s`から{anchorName misc}`Bool`への関数を期待するが、{anchorName DBExprEval}`DBExpr.evaluate`の型は{anchorTerm DBExprEvalType}`Row s → DBExpr s t → t.asType`である。
{anchorName Query}`select`コンストラクタの型が、その式が型{anchorTerm Query}`DBExpr s .bool`を持つことを要求するので、この文脈では{anchorTerm DBExprEvalType}`t.asType`は実際には{anchorName misc}`Bool`である。

標高が500メートルより高いすべての山の頂の高さを見つける問い合わせは次のように書ける。

```anchor Query1
open Query in
def example1 :=
  table mountainDiary |>.select
  (.lt (.const 500) (c! "elevation")) |>.project
  [⟨"elevation", .int⟩] (by repeat constructor)
```

実行すると期待どおりの整数のリストが返る。
```anchor Query1Exec
#eval example1.exec
```
```anchorInfo Query1Exec
[3637, 1519, 2549]
```

観光の計画には、同じ場所にある山と滝の組をすべて対応させると役に立つかもしれない。
これは、両方の表の直積を取り、それらが等しい行だけを選び、次に名前を射影して取り出すことで行える。

```anchor Query2
open Query in
def example2 :=
  let mountain := table mountainDiary |>.prefixWith "mountain"
  let waterfall := table waterfallDiary |>.prefixWith "waterfall"
  mountain.product waterfall (by decide)
    |>.select (.eq (c! "mountain.location") (c! "waterfall.location"))
    |>.project [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩]
      (by repeat constructor)
```
例のデータにはアメリカの滝しか含まれないので、この問い合わせを実行するとアメリカにある山と滝の組が返る。
```anchor Query2Exec
#eval example2.exec
```
```anchorInfo Query2Exec
[("Mount Nebo", "Multnomah Falls"), ("Mount Nebo", "Shoshone Falls"), ("Moscow Mountain", "Multnomah Falls"),
  ("Moscow Mountain", "Shoshone Falls"), ("Mount St. Helens", "Multnomah Falls"),
  ("Mount St. Helens", "Shoshone Falls")]
```

## 出会うかもしれないエラー
%%%
tag := "typed-queries-error-messages"
%%%


起こりうるエラーの多くは{anchorName Query}`Query`の定義によって排除される。
たとえば、{anchorTerm Query2}`"mountain.location"`に加えた修飾を忘れると、列への参照{anchorTerm QueryOops1}`c! "location"`を指し示すコンパイル時のエラーになる。
```anchor QueryOops1
open Query in
def example2 :=
  let mountains := table mountainDiary |>.prefixWith "mountain"
  let waterfalls := table waterfallDiary |>.prefixWith "waterfall"
  mountains.product waterfalls (by simp)
    |>.select (.eq (c! "location") (c! "waterfall.location"))
    |>.project [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩]
      (by repeat constructor)
```
これは優れた手がかりである。
一方、エラーメッセージの文面は、それに基づいて行動するのがかなり難しい。
```anchorError QueryOops1
unsolved goals
mountains : Query (List.map (fun c => { name := "mountain" ++ "." ++ c.name, contains := c.contains }) peak) := ⋯
waterfalls : Query (List.map (fun c => { name := "waterfall" ++ "." ++ c.name, contains := c.contains }) waterfall) := ⋯
⊢ HasCol (List.map (fun c => { name := "waterfall" ++ "." ++ c.name, contains := c.contains }) []) "location" ?m.31
```

同様に、二つの表の名前に接頭辞を加えるのを忘れると、スキーマが実際に重ならない証拠を与えるはずの{kw}`by decide`でエラーになる。
```anchor QueryOops2
open Query in
def example2 :=
  let mountains := table mountainDiary
  let waterfalls := table waterfallDiary
  mountains.product waterfalls (by decide)
    |>.select (.eq (c! "mountain.location") (c! "waterfall.location"))
    |>.project [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩]
      (by repeat constructor)
```
こちらのエラーメッセージはもっと役に立つ。
```anchorError QueryOops2
Tactic `decide` proved that the proposition
  disjoint (List.map Column.name peak) (List.map Column.name waterfall) = true
is false
```

Leanのマクロの仕組みには、問い合わせの便利な構文を与えるだけでなく、エラーメッセージを役に立つものにするために必要なものもすべてそろっている。
残念ながら、Leanのマクロで言語を実装する方法を述べるのはこの本の範囲を超えている。
{anchorName Query}`Query`のような添字付き族は、型付きのデータベース操作ライブラリの利用者向けの画面というより、その核とするのがおそらく最もよい。

# 練習問題
%%%
tag := "typed-query-exercises"
%%%

## 日付
%%%
tag := none
%%%

日付を表す構造体を定義せよ。それを{anchorName DBExpr}`DBType`宇宙に加え、残りのコードもそれに合わせて直せ。必要と思われる{anchorName DBExpr}`DBExpr`の追加のコンストラクタを用意せよ。

## null許容型
%%%
tag := none
%%%

データベースの型を次の構造体で表すことで、null許容の列への対応を問い合わせ言語に加えよ。
```anchor nullable
structure NDBType where
  underlying : DBType
  nullable : Bool

abbrev NDBType.asType (t : NDBType) : Type :=
  if t.nullable then
    Option t.underlying.asType
  else
    t.underlying.asType
```

{anchorName Schema}`Column`と{anchorName DBExpr}`DBExpr`で{anchorName DBExpr}`DBType`の代わりにこの型を使い、SQLの{lit}`NULL`と比較演算子の規則を調べて{anchorName DBExpr}`DBExpr`のコンストラクタの型を決めよ。

## タクティクを試す
%%%
tag := none
%%%


次の型の値を{kw}`by repeat constructor`で見つけるようLeanに頼むとどうなるか。それぞれがその結果になる理由を説明せよ。
 * {anchorName Naturals}`Nat`
 * {anchorTerm misc}`List Nat`
 * {anchorTerm misc}`Vect Nat 4`

 * {anchorTerm misc}`Row []`
 * {anchorTerm misc}`Row [⟨"price", .int⟩]`
 * {anchorTerm misc}`Row peak`
 * {anchorTerm misc}`HasCol [⟨"price", .int⟩, ⟨"price", .int⟩] "price" .int`
