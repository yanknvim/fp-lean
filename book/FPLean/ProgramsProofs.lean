module
public import VersoManual
import FPLean.Examples

import FPLean.ProgramsProofs.TailRecursion
import FPLean.ProgramsProofs.TailRecursionProofs
import FPLean.ProgramsProofs.ArraysTermination
import FPLean.ProgramsProofs.Inequalities
import FPLean.ProgramsProofs.Fin
import FPLean.ProgramsProofs.InsertionSort
import FPLean.ProgramsProofs.SpecialTypes
import FPLean.ProgramsProofs.Summary


open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.TODO"

#doc (Manual) "Programming, Proving, and Performance" =>

この章はプログラミングについてである。
プログラムは正しい結果を計算する必要があるが、効率よくそうする必要もある。
効率のよい関数型プログラムを書くには、データ構造を適切に使う方法と、プログラムを動かすのに要る時間と空間を考える方法の両方を知ることが重要である。

この章は証明についてでもある。
Leanで効率よくプログラミングするのに最も重要なデータ構造の一つは配列だが、配列を安全に使うには、配列の添字が範囲内にあることを証明する必要がある。
さらに、配列に関する興味深い算法のほとんどは構造的再帰の形に従わず、代わりに配列を繰り返し処理する。
これらの算法は停止するが、Leanがそれを自動で調べられるとは限らない。
証明は、プログラムがなぜ停止するかを示すのに使える。

プログラムを速くするために書き換えると、しばしば理解しにくいコードになる。
証明はまた、二つのプログラムが、違う算法や実装の技法を使っていても、常に同じ答えを計算することを示せる。
こうして、遅くて素直なプログラムが、速くて複雑な版の仕様として働ける。

証明とプログラミングを組み合わせると、プログラムを安全かつ効率よくできる。
証明により、実行時の範囲検査を省け、多くの試験が不要になり、実行時の性能の負担を一切持ち込まずに、プログラムへのきわめて高い信頼が得られる。
しかし、プログラムについて定理を証明するのは時間と手間がかかることがあるので、他の道具のほうが経済的なことも多い。

対話的な定理証明は深い話題である。
この章は、Leanでプログラミングするときに実際に現れる証明に向けた、味見程度のものである。
興味深い定理のほとんどはプログラミングと密接には関わらない。
さらに学ぶための資料の一覧は{ref "next-steps"}[次の一歩]を参照してほしい。
しかし、プログラミングを学ぶときと同じく、証明を書くことを学ぶのに実際に手を動かす経験に代わるものはない。始める時である。

{include 1 FPLean.ProgramsProofs.TailRecursion}

{include 1 FPLean.ProgramsProofs.TailRecursionProofs}

{include 1 FPLean.ProgramsProofs.ArraysTermination}

{include 1 FPLean.ProgramsProofs.Inequalities}

{include 1 FPLean.ProgramsProofs.Fin}

{include 1 FPLean.ProgramsProofs.InsertionSort}

{include 1 FPLean.ProgramsProofs.SpecialTypes}

{include 1 FPLean.ProgramsProofs.Summary}
