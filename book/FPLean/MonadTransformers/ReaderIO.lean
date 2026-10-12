module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "DirTree"

#doc (Manual) "Combining IO and Reader" =>
%%%
tag := "io-reader"
%%%

リーダーモナドが役に立つ場面の一つは、多くの再帰呼び出しを通して渡される、アプリケーションの「現在の設定」という考え方があるときである。
そのようなプログラムの例が{lit}`tree`で、現在のディレクトリとその下のディレクトリのファイルを再帰的に表示し、木の構造を文字で示す。
この章の{lit}`tree`の版は、北アメリカ西海岸を飾る雄大なベイマツにちなんで{lit}`doug`と呼ばれ、ディレクトリの構造を示すのにUnicodeの罫線文字か、それに相当するASCII文字を選べる。


たとえば、次のコマンドは{lit}`doug-demo`というディレクトリにディレクトリ構造と空のファイルをいくつか作る。
```commands doug "doug-demo"
$$ cd doug-demo
$ mkdir -p a/b/c
$ mkdir -p a/d
$ mkdir -p a/e/f
$ touch a/b/hello
$ touch a/d/another-file
$ touch a/e/still-another-file-again
```
{lit}`doug`を実行すると次のようになる。
```commands doug "doug-demo"
$ doug
├── doug-demo/
│   ├── a/
│   │   ├── b/
│   │   │   ├── c/
│   │   │   ├── hello
│   │   ├── d/
│   │   │   ├── another-file
│   │   ├── e/
│   │   │   ├── f/
│   │   │   ├── still-another-file-again
```

# 実装
%%%
tag := "reader-io-implementation"
%%%

内部的には、{lit}`doug`はディレクトリ構造を再帰的にたどりながら、設定の値を下へ渡していく。
この設定にはフィールドが二つある。{anchorName Config}`useASCII`は構造を示すのにUnicodeの罫線文字を使うか、ASCIIの縦線と横線を使うかを決め、{anchorName Config}`currentPrefix`は出力の各行の先頭に付ける文字列を入れる。
現在のディレクトリが深くなるにつれ、接頭辞の文字列にディレクトリの中にいることを示す印が積み重なる。
設定は構造体である。

```anchor Config
structure Config where
  useASCII : Bool := false
  currentPrefix : String := ""
```
この構造体にはどちらのフィールドにも既定の定義がある。
既定の{anchorName Config}`Config`は、接頭辞なしでUnicodeの表示を使う。

:::paragraph
{lit}`doug`を起動する利用者は、コマンドライン引数を渡せる必要がある。
使い方の情報は次のとおりである。

```anchor usage
def usage : String :=
  "Usage: doug [--ascii]
Options:
\t--ascii\tUse ASCII characters to display the directory structure"
```
したがって、設定はコマンドライン引数のリストを調べて組み立てられる。

```anchor configFromArgs
def configFromArgs : List String → Option Config
  | [] => some {} -- both fields default
  | ["--ascii"] => some {useASCII := true}
  | _ => none
```
:::

{anchorName OldMain}`main`関数は、設定を使ってディレクトリの中身を表示する内側の作業役{anchorName OldMain}`dirTree`を包むものである。
{anchorName OldMain}`dirTree`を呼ぶ前に、{anchorName OldMain}`main`がコマンドライン引数を処理する役目を負う。
また、オペレーティングシステムに適切な終了コードを返す必要がある。

```anchor OldMain
def main (args : List String) : IO UInt32 := do
  match configFromArgs args with
  | some config =>
    dirTree config (← IO.currentDir)
    pure 0
  | none =>
    IO.eprintln s!"Didn't understand argument(s) {" ".separate args}\n"
    IO.eprintln usage
    pure 1
```
{anchorName OldMain}`IO.eprintln`は、標準エラーに出力する版の{anchorName OldShowFile}`IO.println`である。

すべてのパスをディレクトリの木に表示すべきではない。
特に、{lit}`.`や{lit}`..`という名前のファイルは飛ばすべきである。これらは実際にはファイルそのものではなく、移動に使う仕組みだからである。
表示すべきものには二種類ある。普通のファイルとディレクトリである。

```anchor Entry
inductive Entry where
  | file : String → Entry
  | dir : String → Entry
```
あるファイルを表示すべきか、またどちらの種類の項目かを決めるのに、{lit}`doug`は{anchorName toEntry}`toEntry`を使う。

```anchor toEntry
def toEntry (path : System.FilePath) : IO (Option Entry) := do
  match path.components.getLast? with
  | none => pure (some (.dir ""))
  | some "." | some ".." => pure none
  | some name =>
    pure (some (if (← path.isDir) then .dir name else .file name))
```
{anchorName names}`System.FilePath.components`はパスをパスの構成要素のリストに変換し、名前をディレクトリの区切りで分割する。
最後の構成要素がなければ、そのパスはルートディレクトリである。
最後の構成要素が特別な移動用のファイル（{lit}`.`か{lit}`..`）なら、そのファイルは除くべきである。
そうでなければ、ディレクトリとファイルは対応するコンストラクタで包まれる。

Leanの論理には、ディレクトリの木が有限であることを知る手立てがない。
実際、循環したディレクトリ構造を作れるシステムもある。
したがって{anchorName OldDirTree}`dirTree`は{kw}`partial`として宣言される。

```anchor OldDirTree
partial def dirTree (cfg : Config) (path : System.FilePath) : IO Unit := do
  match ← toEntry path with
  | none => pure ()
  | some (.file name) => showFileName cfg name
  | some (.dir name) =>
    showDirName cfg name
    let contents ← path.readDir
    let newConfig := cfg.inDirectory
    doList (contents.qsort dirLT).toList fun d =>
      dirTree newConfig d.path
```
{anchorName OldDirTree}`toEntry`の呼び出しは{ref "nested-actions"}[入れ子にした動作]である。矢印が他の意味を持ちえない位置、たとえば{kw}`match`では括弧を省ける。
ファイル名が木の項目に対応しないとき（たとえば{lit}`..`であるため）、{anchorName OldDirTree}`dirTree`は何もしない。
ファイル名が普通のファイルを指すとき、{anchorName OldDirTree}`dirTree`は補助関数を呼び、現在の設定でそれを表示する。
ファイル名がディレクトリを指すときは補助関数で表示し、次にその中身を、新しいディレクトリにいることを考慮して接頭辞を延ばした新しい設定で再帰的に表示する。
ディレクトリの中身は出力を決定的にするために並べ替え、比較には{anchorName compareEntries'}`dirLT`を使う。
```anchor compareEntries'
def dirLT (e1 : IO.FS.DirEntry) (e2 : IO.FS.DirEntry) : Bool :=
  e1.fileName < e2.fileName
```

ファイルとディレクトリの名前の表示は、{anchorName OldShowFile}`showFileName`と{anchorName OldShowFile}`showDirName`で行う。

```anchor OldShowFile
def showFileName (cfg : Config) (file : String) : IO Unit := do
  IO.println (cfg.fileName file)

def showDirName (cfg : Config) (dir : String) : IO Unit := do
  IO.println (cfg.dirName dir)
```
これらの補助関数はどちらも、ASCIIとUnicodeのどちらを使うかの設定を考慮する{anchorName filenames}`Config`の関数に委ねる。

```anchor filenames
def Config.preFile (cfg : Config) :=
  if cfg.useASCII then "|--" else "├──"

def Config.preDir (cfg : Config) :=
  if cfg.useASCII then "|  " else "│  "

def Config.fileName (cfg : Config) (file : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {file}"

def Config.dirName (cfg : Config) (dir : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {dir}/"
```
同様に、{anchorName inDirectory}`Config.inDirectory`は接頭辞にディレクトリの印を付け足す。

```anchor inDirectory
def Config.inDirectory (cfg : Config) : Config :=
  {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix}
```

ディレクトリの中身のリストに対してIOの動作を繰り返すのは、{anchorName doList}`doList`で行う。
{anchorName doList}`doList`はリストの動作をすべて実行し、どの動作が返す値にも基づいて制御の流れを決めないので、{anchorName ConfigIO}`Monad`の力は要らず、どの{anchorName doList}`Applicative`でも働く。

```anchor doList
def doList [Applicative f] : List α → (α → f Unit) → f Unit
  | [], _ => pure ()
  | x :: xs, action =>
    action x *>
    doList xs action
```


# 独自のモナドを使う
%%%
tag := "reader-io-custom-monad"
%%%

この{lit}`doug`の実装は動くが、設定を手で受け渡すのは冗長で間違えやすい。
たとえば、間違った設定を下へ渡しても型システムは捕まえない。
リーダーの副作用があれば、手で上書きしない限り同じ設定がすべての再帰呼び出しに渡されることが保証され、コードも冗長でなくなる。

{anchorName ConfigIO}`Config`のリーダーでもある{anchorName ConfigIO}`IO`の版を作るには、まず{ref "custom-environments"}[評価器の例]の手順に従って型とその{anchorName ConfigIO}`Monad`インスタンスを定義する。

```anchor ConfigIO
def ConfigIO (α : Type) : Type :=
  Config → IO α

instance : Monad ConfigIO where
  pure x := fun _ => pure x
  bind result next := fun cfg => do
    let v ← result cfg
    next v cfg
```
この{anchorName ConfigIO}`Monad`インスタンスと{anchorName Reader (module := Examples.Monads.Class)}`Reader`のものとの違いは、{anchorName ConfigIO}`bind`が返す関数の本体で、{anchorName ConfigIO}`result`が返した値に{anchorName ConfigIO}`next`を直接適用するのではなく、{anchorName ConfigIO}`IO`モナドの{kw}`do`記法を使う点である。
{anchorName ConfigIO}`result`が行う{anchorName ConfigIO}`IO`の副作用は、{anchorName ConfigIO}`next`が呼ばれる前に起きねばならず、これは{anchorName ConfigIO}`IO`モナドの{anchorName ConfigIO}`bind`演算子が保証する。
{anchorName ConfigIO}`ConfigIO`が宇宙多相でないのは、その下にある{anchorName ConfigIO}`IO`型も宇宙多相でないためである。

{anchorName ConfigIO}`ConfigIO`の動作を実行するには、設定を与えて{anchorName ConfigIO}`IO`の動作に変換する。

```anchor ConfigIORun
def ConfigIO.run (action : ConfigIO α) (cfg : Config) : IO α :=
  action cfg
```
この関数は実際には必要ない。呼び出し側が設定を直接与えてもよいからである。
しかし、この操作に名前を付けておくと、コードのどの部分がどのモナドで動くつもりなのかが分かりやすくなる。

次に、{anchorName ConfigIO}`ConfigIO`の一部として現在の設定にアクセスする手段を定義する。

```anchor currentConfig
def currentConfig : ConfigIO Config :=
  fun cfg => pure cfg
```
これは{ref "custom-environments"}[評価器の例]の{anchorName Reader (module := Examples.Monads.Class)}`read`とよく似ているが、値を直接返すのではなく{anchorName ConfigIO}`IO`の{anchorName ConfigIO}`pure`で返す点が異なる。
ディレクトリに入ると再帰呼び出しの範囲で現在の設定が変わるので、設定を上書きする手段が必要になる。

```anchor locally
def locally (change : Config → Config) (action : ConfigIO α) : ConfigIO α :=
  fun cfg => action (change cfg)
```

{lit}`doug`で使うコードの多くは設定を必要とせず、{lit}`doug`は標準ライブラリの普通のLeanの{anchorName ConfigIO}`IO`の動作を呼ぶが、それらが{anchorName ConfigIO}`Config`を必要とすることはもちろんない。
普通の{anchorName ConfigIO}`IO`の動作は、設定の引数を無視する{anchorName runIO}`runIO`で実行できる。

```anchor runIO
def runIO (action : IO α) : ConfigIO α :=
  fun _ => action
```

これらの部品があれば、{anchorName MedShowFileDir}`showFileName`と{anchorName MedShowFileDir}`showDirName`を、{anchorName ConfigIO}`ConfigIO`モナドを通して設定の引数を暗黙に受け取るように直せる。
設定を取り出すのに{ref "nested-actions"}[入れ子にした動作]を使い、{anchorName MedShowFileDir}`IO.println`の呼び出しを実際に実行するのに{anchorName runIO}`runIO`を使う。

```anchor MedShowFileDir
def showFileName (file : String) : ConfigIO Unit := do
  runIO (IO.println ((← currentConfig).fileName file))

def showDirName (dir : String) : ConfigIO Unit := do
  runIO (IO.println ((← currentConfig).dirName dir))
```

新しい版の{anchorName MedDirTree}`dirTree`では、{anchorName MedDirTree}`toEntry`と{anchorName MedDirTree}`readDir`の呼び出しを{anchorName runIO}`runIO`で包む。
さらに、新しい設定を組み立ててからプログラマにどれを再帰呼び出しへ渡すか覚えておかせる代わりに、{anchorName MedDirTree}`locally`を使って、変更した設定をプログラムの小さな範囲だけに自然に限定する。その範囲ではそれが*唯一*の有効な設定である。

```anchor MedDirTree
partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
  match ← runIO (toEntry path) with
    | none => pure ()
    | some (.file name) => showFileName name
    | some (.dir name) =>
      showDirName name
      let contents ← runIO path.readDir
      locally (·.inDirectory)
        (doList (contents.qsort dirLT).toList fun d =>
          dirTree d.path)
```

新しい版の{anchorName MedMain}`main`は{anchorName ConfigIORun}`ConfigIO.run`を使い、初期の設定で{anchorName MedMain}`dirTree`を呼び出す。

```anchor MedMain
def main (args : List String) : IO UInt32 := do
    match configFromArgs args with
    | some config =>
      (dirTree (← IO.currentDir)).run config
      pure 0
    | none =>
      IO.eprintln s!"Didn't understand argument(s) {" ".separate args}\n"
      IO.eprintln usage
      pure 1
```

この独自のモナドには、設定を手で渡すことに比べていくつかの利点がある。

 1. 変更したいとき以外は、設定が変わらずに下へ渡されることを確かめやすい。
 2. 設定を先へ渡すという関心事が、ディレクトリの中身を表示する関心事からより明確に分離される。
 3. プログラムが大きくなるにつれ、設定を伝える以外に何もしない中間の層が増えていくが、設定の論理が変わってもこれらの層を書き直す必要がない。

しかし、明らかな欠点もいくつかある。

 1. プログラムが進化してモナドがより多くの機能を要するようになると、{anchorName locally}`locally`や{anchorName currentConfig}`currentConfig`のような基本の演算子をそれぞれ直す必要が出てくる。
 2. 普通の{anchorName ConfigIO}`IO`の動作を{anchorName runIO}`runIO`で包むのは煩わしく、プログラムの流れから注意をそらす。
 3. モナドのインスタンスを手で書くのは繰り返しが多く、別のモナドにリーダーの副作用を加える技法は、文書化と伝達の手間がかかる設計パターンである。

*モナド変換子*と呼ばれる技法を使えば、これらの欠点すべてに対処できる。
モナド変換子はモナドを引数に取り、新しいモナドを返す。
モナド変換子は次のものから成る。
 1. 変換子自体の定義。通常は型から型への関数である。
 2. 内側の型がすでにモナドであることを前提とする{anchorName ConfigIO}`Monad`インスタンス
 3. 内側のモナドの動作を変換後のモナドへ「持ち上げる」演算子。{anchorName runIO}`runIO`に似たものである。

# どのモナドにもリーダーを加える
%%%
tag := "ReaderT"
%%%

{anchorName ConfigIO}`IO`にリーダーの副作用を加えるのは、{anchorName ConfigIO}`ConfigIO`では{anchorTerm ConfigIO}`IO α`を関数型で包むことで行った。
Leanの標準ライブラリには、これを*どの*多相型に対しても行える{anchorName MyReaderT}`ReaderT`という関数がある。

```anchor MyReaderT
def ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) :
    Type (max u v) :=
  ρ → m α
```
その引数は次のとおりである。
 * {anchorName MyReaderT}`ρ`はリーダーから見える環境である。
 * {anchorName MyReaderT}`m`は変換されるモナドで、{anchorName ConfigIO}`IO`などである。
 * {anchorName MyReaderT}`α`はそのモナドの計算が返す値の型である。
{anchorName MyReaderT}`α`と{anchorName MyReaderT}`ρ`が同じ宇宙にあるのは、そのモナドで環境を取り出す演算子の型が{anchorTerm MyReaderTread}`m ρ`になるためである。

:::paragraph
{anchorName MyReaderT}`ReaderT`を使うと、{anchorName ConfigIO}`ConfigIO`は次のようになる。

```anchor ReaderTConfigIO
abbrev ConfigIO (α : Type) : Type := ReaderT Config IO α
```
{kw}`abbrev`とするのは、{anchorName ReaderTConfigIO}`ReaderT`に標準ライブラリで定義された多くの役に立つ機能があり、簡約できない定義ではそれらが隠れてしまうためである。
これらを{anchorName ConfigIO}`ConfigIO`で直接働くようにする責任を負うより、{anchorName ReaderTConfigIO}`ConfigIO`を{anchorTerm ReaderTConfigIO}`ReaderT Config IO`とまったく同じに振る舞わせるほうが簡単である。
:::

:::paragraph
手で書いた{anchorName currentConfig}`currentConfig`はリーダーから環境を取り出していた。
この副作用は、{anchorName MyReaderTread}`ReaderT`のすべての使用に共通する一般的な形として、{anchorName MonadReader}`read`という名前で定義できる。

```anchor MyReaderTread
def read [Monad m] : ReaderT ρ m ρ :=
   fun env => pure env
```
しかし、リーダーの副作用を提供するモナドがすべて{anchorName MyReaderT}`ReaderT`で組み立てられているわけではない。
{anchorName MonadReader}`MonadReader`型クラスを使えば、どのモナドでも{anchorName MonadReader}`read`演算子を提供できる。

```anchor MonadReader
class MonadReader (ρ : outParam (Type u)) (m : Type u → Type v) :
    Type (max (u + 1) v) where
  read : m ρ

instance [Monad m] : MonadReader ρ (ReaderT ρ m) where
  read := fun env => pure env

export MonadReader (read)
```
型{anchorName MonadReader}`ρ`が出力パラメータなのは、あるモナドがリーダーを通して提供する環境の型は通常一つだけなので、モナドが分かっているときにそれを自動で選べばプログラムが書きやすくなるためである。
:::

{anchorName MyReaderT}`ReaderT`の{anchorName ConfigIO}`Monad`インスタンスは{anchorName ConfigIO}`ConfigIO`の{anchorName ConfigIO}`Monad`インスタンスと本質的に同じだが、{anchorName ConfigIO}`IO`が任意のモナドの引数{anchorName MonadMyReaderT}`m`に置き換わっている。

```anchor MonadMyReaderT
instance [Monad m] : Monad (ReaderT ρ m) where
  pure x := fun _ => pure x
  bind result next := fun env => do
    let v ← result env
    next v env
```


次に、{anchorName runIO}`runIO`の使用をなくす。
Leanがモナドの型の食い違いに出会うと、{anchorName MyMonadLift}`MonadLift`という型クラスを使って、実際のモナドを期待されるモナドに自動で変換しようとする。
この処理は型強制の使用に似ている。
{anchorName MyMonadLift}`MonadLift`は次のように定義されている。

```anchor MyMonadLift
class MonadLift (m : Type u → Type v) (n : Type u → Type w) where
  monadLift : {α : Type u} → m α → n α
```
{anchorName MyMonadLift}`monadLift`メソッドはモナド{anchorName MyMonadLift}`m`からモナド{anchorName MyMonadLift}`n`へ変換する。
この処理が「持ち上げ」と呼ばれるのは、埋め込まれたモナドの動作を取り、それを周囲のモナドの動作にするためである。
ここでは{anchorName ConfigIO}`IO`から{anchorTerm ReaderTConfigIO}`ReaderT Config IO`へ「持ち上げる」のに使うが、このインスタンスは*どの*内側のモナド{anchorName MonadLiftReaderT}`m`でも働く。

```anchor MonadLiftReaderT
instance : MonadLift m (ReaderT ρ m) where
  monadLift action := fun _ => action
```
{anchorName MonadLiftReaderT}`monadLift`の実装は{anchorName runIO}`runIO`の実装とよく似ている。
実際、{anchorName runIO}`runIO`を使わずに{anchorName showFileAndDir}`showFileName`と{anchorName showFileAndDir}`showDirName`を定義すれば十分である。

```anchor showFileAndDir
def showFileName (file : String) : ConfigIO Unit := do
  IO.println s!"{(← read).currentPrefix} {file}"

def showDirName (dir : String) : ConfigIO Unit := do
  IO.println s!"{(← read).currentPrefix} {dir}/"
```

元の{anchorName ConfigIO}`ConfigIO`の操作で、{anchorName MyReaderT}`ReaderT`の使用へ移すべきものがもう一つ残っている。{anchorName locally}`locally`である。
その定義は{anchorName MyReaderT}`ReaderT`へ直接移せるが、Leanの標準ライブラリにはより一般的な版がある。
標準の版は{anchorName MyMonadWithReader}`withReader`と呼ばれ、{anchorName MyMonadWithReader}`MonadWithReader`という型クラスの一部である。

```anchor MyMonadWithReader
class MonadWithReader (ρ : outParam (Type u)) (m : Type u → Type v) where
  withReader {α : Type u} : (ρ → ρ) → m α → m α
```
{anchorName MonadReader}`MonadReader`と同じく、環境{anchorName MyMonadWithReader}`ρ`は{anchorName MyMonadWithReader}`outParam`である。
{anchorName exportWithReader}`withReader`操作は export されているので、前に型クラス名を書く必要がない。

```anchor exportWithReader
export MonadWithReader (withReader)
```
{anchorName ReaderTWithReader}`ReaderT`のインスタンスは{anchorName locally}`locally`の定義と本質的に同じである。

```anchor ReaderTWithReader
instance : MonadWithReader ρ (ReaderT ρ m) where
  withReader change action :=
    fun cfg => action (change cfg)
```

これらの定義がそろえば、新しい版の{anchorName readerTDirTree}`dirTree`を書ける。

```anchor readerTDirTree
partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
  match ← toEntry path with
    | none => pure ()
    | some (.file name) => showFileName name
    | some (.dir name) =>
      showDirName name
      let contents ← path.readDir
      withReader (·.inDirectory)
        (doList (contents.qsort dirLT).toList fun d =>
          dirTree d.path)
```
{anchorName locally}`locally`を{anchorName readerTDirTree}`withReader`に置き換えた以外は、以前と同じである。


独自の{anchorName ConfigIO}`ConfigIO`型を{anchorName MonadMyReaderT}`ReaderT`に置き換えても、この節ではコードの行数はあまり減らなかった。
しかし、標準ライブラリの部品を使ってコードを書き直すことには長期的な利点がある。
第一に、{anchorName MyReaderT}`ReaderT`を知っている読み手は、{anchorName ConfigIO}`ConfigIO`の{anchorName ConfigIO}`Monad`インスタンスを理解するのに時間をかけ、モナドの意味自体にさかのぼって考える必要がない。
代わりに、最初の理解に自信を持てる。
次に、モナドにさらに副作用を加える（たとえば各ディレクトリのファイルを数えて最後に件数を表示する状態の副作用）ときのコードの変更がずっと少なくて済む。ライブラリが提供するモナド変換子と{anchorName MonadLiftReaderT}`MonadLift`インスタンスがよく噛み合うためである。
最後に、標準ライブラリに含まれる型クラスの組を使えば、モナド変換子を適用した順序のような細部を気にせずに、さまざまなモナドで働く多相的なコードを書ける。
ある関数がどのモナドでも働くのと同じように、ある種の状態やある種の例外を提供するどのモナドでも働く関数を、特定の具体的なモナドがその状態や例外を提供する*方法*をわざわざ記述せずに書ける。

# 練習問題
%%%
tag := "reader-io-exercises"
%%%

## ドットファイルの表示の制御
%%%
tag := none
%%%

名前がドット文字（{lit}`'.'`）で始まるファイルは通常、バージョン管理のメタデータや設定ファイルのように、普段は隠すべきファイルを表す。
{lit}`doug`を変更し、ドットで始まるファイル名を表示するか隠すかの選択肢を加えよ。
この選択肢は{lit}`-a`というコマンドラインオプションで制御するものとする。

## 開始ディレクトリを引数にする
%%%
tag := none
%%%

{lit}`doug`を変更し、開始ディレクトリを追加のコマンドライン引数として受け取るようにせよ。
