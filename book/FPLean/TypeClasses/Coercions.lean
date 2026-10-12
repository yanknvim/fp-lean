module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true

#doc (Manual) "Coercions" =>
%%%
tag := "coercions"
%%%


数学では、同じ記号を文脈に応じてある対象の異なる側面に使うことがよくある。
たとえば、集合が期待される文脈で環に言及するときは、その環の台集合を指していると解釈される。
プログラミング言語では、ある型の値を別の型の値に自動で変換する規則があるのが普通である。
Javaでは{java}`byte`を自動で{java}`int`に昇格でき、Kotlinではnull非許容型を、その型のnull許容版が期待される文脈で使える。

Leanでは、どちらの目的も{deftech}*型強制*という仕組みが担う。
Leanは、ある型の式を、別の型が期待される文脈で見つけると、型エラーを報告する前にその式を型強制しようとする。
Java、C、Kotlinと違い、型強制は型クラスのインスタンスを定義して拡張できる。

# 文字列とパス
%%%
tag := "string-path-coercion"
%%%

{ref "handling-input"}[{lit}`feline`のソースコード]では、{moduleName}`String`を無名コンストラクタの記法で{moduleName}`FilePath`に変換していた。
実際にはこれは不要だった。Leanは{moduleName}`String`から{moduleName}`FilePath`への型強制を定義しているので、パスが期待される位置に文字列を使える。
関数{anchorTerm readFile}`IO.FS.readFile`の型は{anchorTerm readFile}`System.FilePath → IO String`だが、次のコードはLeanに受け入れられる。

```anchor fileDumper
def fileDumper : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStr "Which file? "
  stdout.flush
  let f := (← stdin.getLine).trimAscii.copy
  stdout.putStrLn s!"'The file {f}' contains:"
  stdout.putStrLn (← IO.FS.readFile f)
```
{moduleName}`String.trimAscii`は文字列の先頭と末尾の空白を取り除き、{tech}[文字列スライス]を返す。そのスライスは{moduleName}`String.Slice.copy`で再び文字列に変換される。
{anchorName fileDumper}`fileDumper`の最後の行では、{moduleName}`String`から{moduleName}`FilePath`への型強制が{anchorName fileDumper}`f`を自動で変換するので、{lit}`IO.FS.readFile ⟨f⟩`と書く必要はない。

# 正の数
%%%
tag := "positive-number-coercion"
%%%

すべての正の数には対応する自然数がある。
先ほど定義した関数{anchorName posToNat}`Pos.toNat`は{moduleName}`Pos`を対応する{moduleName}`Nat`に変換する。

```anchor posToNat
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1
```
型{anchorTerm drop}`{α : Type} → Nat → List α → List α`を持つ関数{anchorName drop}`List.drop`は、リストの先頭を取り除く。
しかし、{anchorName drop}`List.drop`に{moduleName}`Pos`を渡すと型エラーになる。
```anchorTerm dropPos
[1, 2, 3, 4].drop (2 : Pos)
```
```anchorError dropPos
Application type mismatch: The argument
  2
has type
  Pos
but is expected to have type
  Nat
in the application
  List.drop 2
```
{anchorName drop}`List.drop`の作者がこれを型クラスのメソッドにしなかったので、新しいインスタンスを定義して上書きすることはできない。

:::paragraph
{moduleName}`Coe`型クラスは、ある型から別の型への型強制をオーバーロードする方法を記述する。

```anchor Coe
class Coe (α : Type) (β : Type) where
  coe : α → β
```
{anchorTerm CoePosNat}`Coe Pos Nat`のインスタンスがあれば、先ほどのコードが動くようになる。

```anchor CoePosNat
instance : Coe Pos Nat where
  coe x := x.toNat
```
```anchor dropPosCoe
#eval [1, 2, 3, 4].drop (2 : Pos)
```
```anchorInfo dropPosCoe
[3, 4]
```
{kw}`#check`を使うと、舞台裏で使われたインスタンス探索の結果が分かる。
```anchor checkDropPosCoe
#check [1, 2, 3, 4].drop (2 : Pos)
```
```anchorInfo checkDropPosCoe
List.drop (Pos.toNat 2) [1, 2, 3, 4] : List Nat
```
:::

# 型強制の連鎖
%%%
tag := "chaining-coercions"
%%%

型強制を探すとき、Leanはより小さな型強制の連鎖から一つの型強制を組み立てようとする。
たとえば、{anchorName chapterIntro}`Nat`から{anchorName chapterIntro}`Int`への型強制はすでにある。
そのインスタンスと{anchorTerm CoePosNat}`Coe Pos Nat`のインスタンスを組み合わせることで、次のコードが受け入れられる。

```anchor posInt
def oneInt : Int := Pos.one
```
この定義は二つの型強制を使っている。{anchorTerm CoePosNat}`Pos`から{anchorTerm CoePosNat}`Nat`へ、次に{anchorTerm CoePosNat}`Nat`から{anchorTerm chapterIntro}`Int`へである。

Leanコンパイラは、循環する型強制があっても行き詰まらない。
たとえば、二つの型{anchorName CoercionCycle}`A`と{anchorName CoercionCycle}`B`が互いに型強制できるとしても、その相互の型強制を使って経路を見つけられる。

```anchor CoercionCycle
inductive A where
  | a

inductive B where
  | b

instance : Coe A B where
  coe _ := B.b

instance : Coe B A where
  coe _ := A.a

instance : Coe Unit A where
  coe _ := A.a

def coercedToB : B := ()
```
念のため、二重の括弧{anchorTerm CoercionCycle}`()`はコンストラクタ{anchorName chapterIntro}`Unit.unit`の略である。
{anchorTerm ReprB}`deriving instance Repr for B`で{anchorTerm ReprBTm}`Repr B`のインスタンスを導出すると、
```anchor coercedToBEval
#eval coercedToB
```
次のようになる。
```anchorInfo coercedToBEval
B.b
```

:::paragraph
{anchorName CoeOption}`Option`型は、C#やKotlinのnull許容型と同じように使える。コンストラクタ{anchorName NEListGetHuh}`none`が値の欠如を表す。
Leanの標準ライブラリは、任意の型{anchorName CoeOption}`α`から{anchorTerm CoeOption}`Option α`への型強制を定義しており、値が{anchorName CoeOption}`some`で包まれる。
これにより、{anchorName CoeOption}`some`を省略できるので、オプション型をnull許容型にさらに近い形で使える。
たとえば、リストの最後の要素を求める関数{anchorName lastHuh}`List.last?`は、戻り値{anchorName lastHuh}`x`を{anchorName CoeOption}`some`で包まずに書ける。

```anchor lastHuh
def List.last? : List α → Option α
  | [] => none
  | [x] => x
  | _ :: x :: xs => last? (x :: xs)
```
インスタンス探索がその型強制を見つけ、引数を{anchorName CoeOption}`some`で包む{anchorName Coe}`coe`の呼び出しを挿入する。
この型強制は連鎖できるので、{anchorName CoeOption}`Option`を入れ子に使っても{anchorName CoeOption}`some`を入れ子に書かなくてよい。

```anchor perhapsPerhapsPerhaps
def perhapsPerhapsPerhaps : Option (Option (Option String)) :=
  "Please don't tell me"
```
:::

:::paragraph
型強制が自動で働くのは、Leanが推論した型と、プログラムの残りの部分から課される型が食い違ったときだけである。
他の種類のエラーの場合は、型強制は働かない。
たとえば、エラーがインスタンスの欠如である場合は、型強制は使われない。
```anchor ofNatBeforeCoe
def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  392
```
```anchorError ofNatBeforeCoe
failed to synthesize instance of type class
  OfNat (Option (Option (Option Nat))) 392
numerals are polymorphic in Lean, but the numeral `392` cannot be used in a context where the expected type is
  Option (Option (Option Nat))
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
:::

:::paragraph
これは、{moduleName}`OfNat`に使う型を手で指定すれば避けられる。

```anchor perhapsPerhapsPerhapsNat
def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  (392 : Nat)
```
さらに、上矢印を使って型強制を手で挿入できる。

```anchor perhapsPerhapsPerhapsNatUp
def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  ↑(392 : Nat)
```
場合によっては、Leanが正しいインスタンスを見つけるようにするのに使える。
プログラマの意図も伝わりやすくなる。
:::

# 空でないリストと依存型強制
%%%
tag := "CoeDep"
%%%

{anchorTerm chapterIntro}`Coe α β`のインスタンスは、型{anchorName chapterIntro}`β`が、型{anchorName chapterIntro}`α`のどの値も表せる値を持つときに意味をなす。
{moduleName}`Nat`から{moduleName}`Int`への型強制は意味をなす。型{moduleName}`Int`がすべての自然数を含むためである。しかし{moduleName}`Int`から{moduleName}`Nat`への型強制はよくない。{moduleName}`Nat`が負の数を含まないためである。
同様に、空でないリストから普通のリストへの型強制は意味をなす。{moduleName}`List`型がすべての空でないリストを表せるためである。

```anchor CoeNEList
instance : Coe (NonEmptyList α) (List α) where
  coe
    | { head := x, tail := xs } => x :: xs
```
これにより、空でないリストを{moduleName}`List`のAPI全体で使える。

一方、{anchorTerm coeNope}`Coe (List α) (NonEmptyList α)`のインスタンスは書けない。空のリストを表せる空でないリストは存在しないためである。
この制限は、*依存型強制*と呼ばれる別の種類の型強制を使えば避けられる。
依存型強制は、ある型から別の型へ型強制できるかどうかが、型強制する具体的な値に依存するときに使える。
{anchorName OfNat}`OfNat`型クラスがオーバーロードする具体的な{moduleName}`Nat`を引数に取るのと同じように、依存型強制は型強制する値を引数に取る。

```anchor CoeDep
class CoeDep (α : Type) (x : α) (β : Type) where
  coe : β
```
これは、値にさらに型クラスの制約を課すか、特定のコンストラクタを直接書くことで、特定の値だけを選ぶ機会である。
たとえば、実際には空でない{moduleName}`List`は{moduleName}`NonEmptyList`に型強制できる。

```anchor CoeDepListNEList
instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := { head := x, tail := xs }
```

# 型への型強制
%%%
tag := "CoeSort"
%%%

数学では、集合にさらに構造を加えたものから成る概念がよくある。
たとえばモノイドは、ある集合$`S`、$`S`の要素$`s`、$`S`上の結合的な二項演算子から成り、$`s`がその演算子の左右で中立である。
$`S`をそのモノイドの「台集合」と呼ぶ。
自然数と0と加法はモノイドになる。加法が結合的で、どの数に0を足しても変わらないためである。
同様に、自然数と1と乗法もモノイドになる。
モノイドは関数型プログラミングでも広く使われる。リスト、空のリスト、連結演算子がモノイドになり、文字列、空文字列、文字列の連結もそうである。

```anchor Monoid
structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier

def natMulMonoid : Monoid :=
  { Carrier := Nat, neutral := 1, op := (· * ·) }

def natAddMonoid : Monoid :=
  { Carrier := Nat, neutral := 0, op := (· + ·) }

def stringMonoid : Monoid :=
  { Carrier := String, neutral := "", op := String.append }

def listMonoid (α : Type) : Monoid :=
  { Carrier := List α, neutral := [], op := List.append }
```
モノイドが与えられれば、リストの要素を一度の走査でモノイドの台集合の値に変換し、モノイドの演算子でまとめる{anchorName firstFoldMap}`foldMap`関数を書ける。
モノイドには中立元があるので、リストが空のときに返す自然な結果があり、演算子が結合的なので、その関数の利用者は再帰関数が要素を左から右にまとめるか右から左にまとめるかを気にしなくてよい。

```anchor firstFoldMap
def foldMap (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec go (soFar : M.Carrier) : List α → M.Carrier
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs
```

モノイドが三つの別々の情報から成っていても、その集合を指すのにモノイドの名前を使うのが普通である。
「*A*をモノイドとし、*x*と*y*をその台集合の要素とする」と言う代わりに、「*A*をモノイドとし、*x*と*y*を*A*の要素とする」と言うのが普通である。
この習慣は、モノイドからその台集合への新しい種類の型強制を定義することでLeanに表せる。

{anchorName CoeMonoid}`CoeSort`クラスは{anchorName CoePosNat}`Coe`クラスとほぼ同じだが、型強制の対象が*ソート*、つまり{anchorTerm chapterIntro}`Type`か{anchorTerm chapterIntro}`Prop`でなければならない点が異なる。
Leanで*ソート*とは、他の型を分類するこれらの型を指す。{anchorTerm Coe}`Type`はデータを分類する型を分類し、{anchorTerm chapterIntro}`Prop`は真理の証拠を分類する命題を分類する。
型の食い違いが起きたときに{anchorName CoePosNat}`Coe`が調べられるのと同じように、ソートが期待される文脈でソート以外のものが与えられたときに{anchorName CoeMonoid}`CoeSort`が使われる。

モノイドからその台集合への型強制は、台を取り出す。

```anchor CoeMonoid
instance : CoeSort Monoid Type where
  coe m := m.Carrier
```
この型強制により、型シグネチャが簡潔になる。

```anchor foldMap
def foldMap (M : Monoid) (f : α → M) (xs : List α) : M :=
  let rec go (soFar : M) : List α → M
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs
```

{anchorName CoeMonoid}`CoeSort`のもう一つの役に立つ例は、{anchorName types}`Bool`と{anchorTerm chapterIntro}`Prop`の隔たりを埋めるのに使う。
{ref "equality-and-ordering"}[順序と等価性の節]で述べたように、Leanの{kw}`if`式は条件が{anchorName types}`Bool`ではなく決定可能な命題であることを期待する。
しかし、プログラムは通常、真偽値に基づいて分岐できる必要がある。
二種類の{kw}`if`式を用意する代わりに、Leanの標準ライブラリは、{anchorName types}`Bool`から、その{anchorName types}`Bool`が{anchorName types}`true`に等しいという命題への型強制を定義している。

```anchor CoeBoolProp
instance : CoeSort Bool Prop where
  coe b := b = true
```
この場合のソートは{anchorTerm chapterIntro}`Type`ではなく{anchorTerm chapterIntro}`Prop`である。

# 関数への型強制
%%%
tag := "CoeFun"
%%%

プログラミングでよく現れるデータ型の多くは、関数と、それについての追加情報から成る。
たとえば、関数にログに出す名前や設定データが添えられることがある。
さらに、{anchorName Monoid}`Monoid`の例のように構造体のフィールドに型を入れるのは、ある操作の実装方法が複数あり、型クラスでできる以上の手動の制御が要る場面で意味をなす。
たとえば、JSONシリアライザが出力する値の細かい点は、別のアプリケーションが特定の形式を期待するため重要になることがある。
関数自体が設定データだけから導けることもある。

{anchorName CoeFun}`CoeFun`という型クラスは、関数でない型の値を関数型に変換できる。
{anchorName CoeFun}`CoeFun`は二つの引数を取る。一つ目は値を関数に変換する対象の型、二つ目は対象となる関数型を決める出力パラメータである。

```anchor CoeFun
class CoeFun (α : Type) (makeFunctionType : outParam (α → Type)) where
  coe : (x : α) → makeFunctionType x
```
二つ目の引数は、型を計算する関数そのものである。
Leanでは型は第一級であり、他のものと同じように関数に渡したり関数から返したりできる。

たとえば、引数に一定量を足す関数は、実際の関数を定義する代わりに、足す量を包んだものとして表せる。

```anchor Adder
structure Adder where
  howMuch : Nat
```
引数に5を足す関数は、{anchorName Adder}`howMuch`フィールドに{anchorTerm add5}`5`を入れる。

```anchor add5
def add5 : Adder := ⟨5⟩
```
この{anchorName Adder}`Adder`型は関数ではないので、引数に適用するとエラーになる。
```anchor add5notfun
#eval add5 3
```
```anchorError add5notfun
Function expected at
  add5
but this term has type
  Adder

Note: Expected a function because this term is being applied to the argument
  3
```
{anchorName CoeFunAdder}`CoeFun`のインスタンスを定義すると、Leanがその加算器を{anchorTerm CoeFunAdder}`Nat → Nat`型の関数に変換する。

```anchor CoeFunAdder
instance : CoeFun Adder (fun _ => Nat → Nat) where
  coe a := (· + a.howMuch)
```
```anchor add53
#eval add5 3
```
```anchorInfo add53
8
```
どの{anchorName CoeFunAdder}`Adder`も{anchorTerm CoeFunAdder}`Nat → Nat`の関数に変換すべきなので、{anchorName CoeFunAdder}`CoeFun`の二つ目の引数の引数は無視された。

:::paragraph
適切な関数型を決めるのに値そのものが要る場合は、{anchorName CoeFunAdder}`CoeFun`の二つ目の引数は無視できない。
たとえば、JSONの値を次のように表すとする。

```anchor JSON
inductive JSON where
  | true : JSON
  | false : JSON
  | null : JSON
  | string : String → JSON
  | number : Float → JSON
  | object : List (String × JSON) → JSON
  | array : List JSON → JSON
```
JSONシリアライザは、シリアライズできる型と、シリアライズのコード自体を組にした構造体である。

```anchor Serializer
structure Serializer where
  Contents : Type
  serialize : Contents → JSON
```
文字列のシリアライザは、与えられた文字列を{anchorName StrSer}`JSON.string`コンストラクタで包むだけでよい。

```anchor StrSer
def Str : Serializer :=
  { Contents := String,
    serialize := JSON.string
  }
```
:::

:::paragraph
JSONシリアライザを、引数をシリアライズする関数として見るには、シリアライズできるデータの内側の型を取り出す必要がある。

```anchor CoeFunSer
instance : CoeFun Serializer (fun s => s.Contents → JSON) where
  coe s := s.serialize
```
このインスタンスがあれば、シリアライザを引数に直接適用できる。

```anchor buildResponse
def buildResponse (title : String) (R : Serializer)
    (record : R.Contents) : JSON :=
  JSON.object [
    ("title", JSON.string title),
    ("status", JSON.number 200),
    ("record", R record)
  ]
```
シリアライザは{anchorName buildResponseOut}`buildResponse`に直接渡せる。
```anchor buildResponseOut
#eval buildResponse "Functional Programming in Lean" Str "Programming is fun!"
```
```anchorInfo buildResponseOut
JSON.object
  [("title", JSON.string "Functional Programming in Lean"),
   ("status", JSON.number 200.000000),
   ("record", JSON.string "Programming is fun!")]
```
:::

## 補足: JSONを文字列として見る
%%%
tag := "json-string"
%%%

JSONをLeanのオブジェクトとして符号化したものは、少し分かりにくいことがある。
シリアライズした応答が期待どおりかを確かめるには、{anchorName JSON}`JSON`から{anchorName dropDecimals}`String`への単純な変換器があると便利である。
まず、数の表示を簡単にする。
{anchorName JSON}`JSON`は整数と浮動小数点数を区別せず、どちらも{anchorName JSON}`Float`型で表す。
Leanでは、{anchorName chapterIntro}`Float.toString`が末尾に0をいくつも付ける。
```anchor fiveZeros
#eval (5 : Float).toString
```
```anchorInfo fiveZeros
"5.000000"
```
解決策は、末尾の0をすべて取り除き、その後に残る小数点も取り除く小さな関数を書くことである。

```anchor dropDecimals
def dropDecimals (numString : String) : String :=
  if numString.contains '.' then
    let noTrailingZeros := numString.dropEndWhile (· == '0')
    (noTrailingZeros.dropEndWhile (· == '.')).copy
  else numString
```
この定義により、{anchorTerm dropDecimalExample}`dropDecimals (5 : Float).toString`は{anchorTerm dropDecimalExample}`5`に、{anchorTerm dropDecimalExample2}`dropDecimals (5.2 : Float).toString`は{anchorTerm dropDecimalExample2}`5.2`になる。

次に、文字列のリストを区切り文字を挟んで連結する補助関数を定義する。

```anchor Stringseparate
def String.separate (sep : String) (strings : List String) : String :=
  match strings with
  | [] => ""
  | x :: xs => String.join (x :: xs.map (sep ++ ·))
```
この関数は、JSONの配列やオブジェクトで要素をコンマで区切るのに役に立つ。
{anchorTerm sep2ex}`", ".separate ["1", "2"]`は{anchorInfo sep2ex}`"1, 2"`に、{anchorTerm sep1ex}`", ".separate ["1"]`は{anchorInfo sep1ex}`"1"`に、{anchorTerm sep0ex}`", ".separate []`は{anchorInfo sep0ex}`""`になる。
Leanの標準ライブラリでは、この関数は{anchorName chapterIntro}`String.intercalate`という名前である。

最後に、JSONの文字列のためのエスケープ処理が要る。{anchorTerm chapterIntro}`"Hello!"`を含むLeanの文字列を{anchorTerm escapeQuotes}`"\"Hello!\""`として出力できるようにするためである。
幸い、LeanコンパイラにはJSON文字列をエスケープする内部関数がすでにあり、{anchorName escapeQuotes}`Lean.Json.escape`という。
この関数を使うには、ファイルの先頭に{lit}`import Lean`を加える。

{anchorName JSONasString}`JSON`の値から文字列を作る関数は{kw}`partial`として宣言されている。Leanがその停止性を見抜けないためである。
{anchorName JSONasString}`asString`への再帰呼び出しが、{anchorName chapterIntro}`List.map`で適用される関数の中で起きており、この形の再帰はLeanがより小さい値に対して行われていると見抜けないほど複雑なのである。
JSONの文字列を作るだけで、その処理について数学的に推論する必要がないアプリケーションでは、関数が{kw}`partial`でも問題は起きにくい。

```anchor JSONasString
partial def JSON.asString (val : JSON) : String :=
  match val with
  | true => "true"
  | false => "false"
  | null => "null"
  | string s => "\"" ++ Lean.Json.escape s ++ "\""
  | number n => dropDecimals n.toString
  | object members =>
    let memberToString mem :=
      "\"" ++ Lean.Json.escape mem.fst ++ "\": " ++ asString mem.snd
    "{" ++ ", ".separate (members.map memberToString) ++ "}"
  | array elements =>
    "[" ++ ", ".separate (elements.map asString) ++ "]"
```
この定義により、シリアライズの出力が読みやすくなる。
```anchor buildResponseStr
#eval (buildResponse "Functional Programming in Lean" Str "Programming is fun!").asString
```
```anchorInfo buildResponseStr
"{\"title\": \"Functional Programming in Lean\", \"status\": 200, \"record\": \"Programming is fun!\"}"
```


# 出会うかもしれないメッセージ
%%%
tag := "coercion-messages"
%%%

自然数のリテラルは{anchorName OfNat}`OfNat`型クラスでオーバーロードされている。
型強制が働くのは型が一致しない場合であり、インスタンスが欠けている場合ではないので、ある型に{anchorName OfNat}`OfNat`のインスタンスがなくても、{moduleName}`Nat`からの型強制は適用されない。
```anchor ofNatBeforeCoe
def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  392
```
```anchorError ofNatBeforeCoe
failed to synthesize instance of type class
  OfNat (Option (Option (Option Nat))) 392
numerals are polymorphic in Lean, but the numeral `392` cannot be used in a context where the expected type is
  Option (Option (Option Nat))
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

# 設計上の考慮
%%%
tag := "coercion-design-considerations"
%%%

型強制は強力な道具であり、責任をもって使うべきである。
一方では、型強制によって、APIが対象分野の日常的な規則に自然に従えるようになる。
手動の変換関数が煩雑に散らばったプログラムと、明快なプログラムの違いになりうる。
AbelsonとSussmanは_Structure and Interpretation of Computer Programs_（MIT Press、1996年）の序文で次のように書いている。

> プログラムは人が読むために書かれなければならず、機械が実行するのは副次的なことにすぎない。

賢く使えば、型強制は読みやすいコードを実現し、分野の専門家とのやり取りの土台になる貴重な手段である。
しかし、型強制に大きく頼るAPIには、いくつか重要な制限がある。
自分のライブラリで型強制を使う前に、これらの制限をよく考えるとよい。

第一に、型強制の型クラスには出力パラメータがないので、型強制が適用されるのは、関わる型をすべてLeanが把握できるだけの型情報がある文脈だけである。つまり、関数の戻り値の型注釈があるかどうかが、型エラーになるか型強制がうまく働くかの違いになる。
たとえば、空でないリストからリストへの型強制があるので、次のプログラムは動く。

```anchor lastSpiderA
def lastSpider : Option String :=
  List.getLast? idahoSpiders
```
一方、型注釈を省くと結果の型が分からず、Leanは型強制を見つけられない。
```anchor lastSpiderB
def lastSpider :=
  List.getLast? idahoSpiders
```
```anchorError lastSpiderB
Application type mismatch: The argument
  idahoSpiders
has type
  NonEmptyList String
but is expected to have type
  List ?m.3
in the application
  List.getLast? idahoSpiders
```
より一般に、何らかの理由で型強制が適用されないと、利用者には元の型エラーが返るので、型強制の連鎖を調べるのが難しくなる。

最後に、型強制はフィールドアクセサの記法の文脈では適用されない。
つまり、型強制が必要な式と不要な式の間には依然として重要な違いがあり、その違いはAPIの利用者に見えてしまう。
