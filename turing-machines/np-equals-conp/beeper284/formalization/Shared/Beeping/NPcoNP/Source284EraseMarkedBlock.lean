import Shared.Beeping.NPcoNP.Source284ScratchMarkedLoop
import Shared.Beeping.NPcoNP.Source284ClearOddMarked
import Shared.Beeping.NPcoNP.Source284EraseZeroBlock

/-! Erase a zero block and its sentinel while recording every cleared cell
as a one in the scratch suffix. The marks can later drive a paid shift. -/
set_option maxRecDepth 4096
namespace Shared.Beeping.NPcoNP.Source284EraseMarkedBlock

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284ScratchMarkedLoop (marks)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284ScratchMarkedLoop.table (Source284ClearOddMarked.table continuation)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (30+states) (table continuation) := by
  have hc := Source284ClearOddMarked.closed states continuation hn hv
  have hl := Source284ScratchMarkedLoop.closed (16+states)
    (Source284ClearOddMarked.table continuation) (by omega) hc
  simpa [table,show 14+(16+states)=30+states by omega] using hl

theorem marks_push (count tail : Nat) : marks count (2*tail+1) = 2*marks count tail+1 := by
  induction count generalizing tail with
  | zero => rfl
  | succ count ih => simp only [marks,ih]

theorem marks_succ (count tail : Nat) : marks (count+1) tail = 2*marks count tail+1 := by
  simp only [marks,marks_push]

/-- Every cleared zero and the sentinel generate exactly one marked cell. -/
theorem erase_then (continuation : Nat → Bool → Row) (zeros : Nat) (w : List Bool)
    (certificate tail fuel : Nat) :
    run (table continuation) ⟨2^(zeros+1)*(2*certificate+1),2*flipped w tail,some 0⟩
      (Source284EraseZeroBlock.cost zeros w.length+fuel) =
    shiftConfig 30 (run continuation
      ⟨certificate,2*flipped w (marks (zeros+2) tail),some 0⟩ fuel) := by
  have ht : Source284EraseZeroBlock.cost zeros w.length+fuel =
      (zeros+1)*(8*w.length+11)+(8*w.length+13+fuel) := by
    simp [Source284EraseZeroBlock.cost]; omega
  rw [ht]
  unfold table
  rw [Source284ScratchMarkedLoop.countdown_after,Source284ClearOddMarked.clear_then,
    Source284SourceRelocation.shiftConfig_add]
  have hm : marks (zeros+2) tail = 2*marks (zeros+1) tail+1 := by
    simpa [Nat.add_assoc] using marks_succ (zeros+1) tail
  rw [hm]

end Shared.Beeping.NPcoNP.Source284EraseMarkedBlock
