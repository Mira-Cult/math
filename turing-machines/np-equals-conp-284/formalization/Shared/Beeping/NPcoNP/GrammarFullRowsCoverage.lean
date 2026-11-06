import Shared.Beeping.NPcoNP.GrammarFullRowsShard00
import Shared.Beeping.NPcoNP.GrammarFullRowsShard01
import Shared.Beeping.NPcoNP.GrammarFullRowsShard02
import Shared.Beeping.NPcoNP.GrammarFullRowsShard03
import Shared.Beeping.NPcoNP.GrammarFullRowsShard04
import Shared.Beeping.NPcoNP.GrammarFullRowsShard05
import Shared.Beeping.NPcoNP.GrammarFullRowsShard06
import Shared.Beeping.NPcoNP.GrammarFullRowsShard07
import Shared.Beeping.NPcoNP.GrammarFullRowsShard08
import Shared.Beeping.NPcoNP.GrammarFullRowsShard09
import Shared.Beeping.NPcoNP.GrammarFullRowsShard10
import Shared.Beeping.NPcoNP.GrammarFullRowsShard11
import Shared.Beeping.NPcoNP.GrammarFullRowsShard12
import Shared.Beeping.NPcoNP.GrammarFullRowsShard13
import Shared.Beeping.NPcoNP.GrammarFullRowsShard14
import Shared.Beeping.NPcoNP.GrammarFullRowsShard15
import Shared.Beeping.NPcoNP.GrammarFullRowsShard16
import Shared.Beeping.NPcoNP.GrammarFullRowsShard17
import Shared.Beeping.NPcoNP.GrammarFullRowsShard18
import Shared.Beeping.NPcoNP.GrammarFullRowsShard19
import Shared.Beeping.NPcoNP.GrammarFullRowsShard20
import Shared.Beeping.NPcoNP.GrammarFullRowsShard21
import Shared.Beeping.NPcoNP.GrammarFullRowsShard22
import Shared.Beeping.NPcoNP.GrammarFullRowsShard23
import Shared.Beeping.NPcoNP.GrammarFullRowsShard24
import Shared.Beeping.NPcoNP.GrammarFullRowsShard25
import Shared.Beeping.NPcoNP.GrammarFullRowsShard26
import Shared.Beeping.NPcoNP.GrammarFullRowsShard27

/-! Coverage of every row in the checked Lean AST expansion.
The JSON-byte and producer-algorithm bindings remain separate. -/
namespace Shared.Beeping.NPcoNP.GrammarFullRowsCoverage
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace

set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

theorem allRows (i : Nat) (hi : i < traceState557.acc.leaves.size) :
    indexedRowCheck traceState557.acc producerFullRows i = true := by
  have hbound : i < 279 := by simpa [producerLeafCount] using hi
  by_cases h0 : i < 10
  · exact indexedRowShard_sound _ _ 0 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard00.checked (by omega) (by omega)
  by_cases h1 : i < 20
  · exact indexedRowShard_sound _ _ 10 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard01.checked (by omega) (by omega)
  by_cases h2 : i < 30
  · exact indexedRowShard_sound _ _ 20 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard02.checked (by omega) (by omega)
  by_cases h3 : i < 40
  · exact indexedRowShard_sound _ _ 30 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard03.checked (by omega) (by omega)
  by_cases h4 : i < 50
  · exact indexedRowShard_sound _ _ 40 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard04.checked (by omega) (by omega)
  by_cases h5 : i < 60
  · exact indexedRowShard_sound _ _ 50 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard05.checked (by omega) (by omega)
  by_cases h6 : i < 70
  · exact indexedRowShard_sound _ _ 60 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard06.checked (by omega) (by omega)
  by_cases h7 : i < 80
  · exact indexedRowShard_sound _ _ 70 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard07.checked (by omega) (by omega)
  by_cases h8 : i < 90
  · exact indexedRowShard_sound _ _ 80 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard08.checked (by omega) (by omega)
  by_cases h9 : i < 100
  · exact indexedRowShard_sound _ _ 90 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard09.checked (by omega) (by omega)
  by_cases h10 : i < 110
  · exact indexedRowShard_sound _ _ 100 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard10.checked (by omega) (by omega)
  by_cases h11 : i < 120
  · exact indexedRowShard_sound _ _ 110 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard11.checked (by omega) (by omega)
  by_cases h12 : i < 130
  · exact indexedRowShard_sound _ _ 120 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard12.checked (by omega) (by omega)
  by_cases h13 : i < 140
  · exact indexedRowShard_sound _ _ 130 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard13.checked (by omega) (by omega)
  by_cases h14 : i < 150
  · exact indexedRowShard_sound _ _ 140 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard14.checked (by omega) (by omega)
  by_cases h15 : i < 160
  · exact indexedRowShard_sound _ _ 150 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard15.checked (by omega) (by omega)
  by_cases h16 : i < 170
  · exact indexedRowShard_sound _ _ 160 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard16.checked (by omega) (by omega)
  by_cases h17 : i < 180
  · exact indexedRowShard_sound _ _ 170 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard17.checked (by omega) (by omega)
  by_cases h18 : i < 190
  · exact indexedRowShard_sound _ _ 180 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard18.checked (by omega) (by omega)
  by_cases h19 : i < 200
  · exact indexedRowShard_sound _ _ 190 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard19.checked (by omega) (by omega)
  by_cases h20 : i < 210
  · exact indexedRowShard_sound _ _ 200 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard20.checked (by omega) (by omega)
  by_cases h21 : i < 220
  · exact indexedRowShard_sound _ _ 210 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard21.checked (by omega) (by omega)
  by_cases h22 : i < 230
  · exact indexedRowShard_sound _ _ 220 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard22.checked (by omega) (by omega)
  by_cases h23 : i < 240
  · exact indexedRowShard_sound _ _ 230 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard23.checked (by omega) (by omega)
  by_cases h24 : i < 250
  · exact indexedRowShard_sound _ _ 240 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard24.checked (by omega) (by omega)
  by_cases h25 : i < 260
  · exact indexedRowShard_sound _ _ 250 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard25.checked (by omega) (by omega)
  by_cases h26 : i < 270
  · exact indexedRowShard_sound _ _ 260 10 i Shared.Beeping.NPcoNP.GrammarFullRowsShard26.checked (by omega) (by omega)
  exact indexedRowShard_sound _ _ 270 9 i Shared.Beeping.NPcoNP.GrammarFullRowsShard27.checked (by omega) (by omega)

theorem producerFullGraph : fullGraph producerGrammar 53 = some producerFullRows := by
  apply fullGraph_of_checked_rows producerGrammar 53 traceState557.acc producerFullRows producerExpand
  · rw [producerLeafCount]; rfl
  · exact allRows

end Shared.Beeping.NPcoNP.GrammarFullRowsCoverage
