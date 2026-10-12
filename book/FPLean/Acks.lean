module
public import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.TODO"

#doc (Manual) "Acknowledgments" =>
%%%
number := false
%%%


この無料のオンライン書籍は、マイクロソフトリサーチの惜しみない支援によって実現した。同社が執筆の費用を負担し、無償での公開を可能にしてくれた。
執筆の過程では、私の質問に答えるため、またLeanを使いやすくするために、Lean開発チームの知見を惜しみなく提供してくれた。
とくに、Leonardo de Mouraはこの企画を立ち上げ、私が書き始めるのを助けてくれた。Chris LovettはCIとデプロイの自動化を整え、試読者として多くの助言をくれた。Gabriel Ebnerは技術的なレビューを担当し、Sarah Smithは事務面を円滑に進めてくれた。Vanessa Rodriguezは、ソースコードのハイライト表示ライブラリとiOS版Safariの特定のバージョンの間で起きる厄介な問題の診断に協力してくれた。

本書の執筆には、通常の勤務時間外の時間を多く費やした。
妻のEllie Thrane Christiansenは、いつもよりずっと大きな割合で家庭のことを引き受けてくれた。それがなければ、この本は存在しなかった。
毎週1日多く作業することは、家族にとって楽ではなかった。執筆中の忍耐と支えに感謝する。

Leanをとりまくオンラインコミュニティは、技術面でも気持ちの面でも、この企画を熱心に支えてくれた。
とくにSebastian Ullrichには、Leanのメタプログラミングを学ぶ際に重要な助けをいただいた。おかげで、エラーメッセージの文面をCIで検査しつつ、本編にも簡単に取り込めるようにするコードを書くことができた。
新しい版を公開すると、数時間のうちに読者たちが誤りを見つけ、提案を寄せ、励ましてくれた。
文体面でも技術面でも多くの提案をくれた、次の方々に感謝する。Arien Malec、Asta Halkjær From、Bulhwi Cha、Craig Stuntz、Daniel Fabian、Evgenia Karunus、eyelash、Floris van Doorn、František Silváši、Henrik Böving、Ian Young、Jeremy Salwen、Jireh Loreaux、Kevin Buzzard、Lars Ericson、Liu Yuxi、Mac Malone、Malcolm Langfield、Mario Carneiro、Newell Jensen、Patrick Massot、Paul Chisholm、Pietro Monticone、Tomas Puverle、Yaël Dillies、Zhiyuan Bao、Zyad Hassan。
