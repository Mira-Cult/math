import Shared.Beeping.NPcoNP.Source284CheckpointMarkedWorkspace
import Shared.Beeping.NPcoNP.Source284CheckpointRestored

/-! Restore the original certificate and exact old guard gap while keeping
the independently generated marked workspace counter behind its separator. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284CheckpointMarkedRestored

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284CheckpointWorkspace
open Shared.Beeping.NPcoNP.Source284CheckpointMarkedWorkspace
open Shared.Beeping.NPcoNP.Source284ProductIteration (historyAfter)
open Shared.Beeping.NPcoNP.Source284ScratchMarkedLoop (marks)
open Shared.Beeping.NPcoNP.Source284PolynomialMarkedCleanup (count)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

def shortZeros (k n : Nat) : Nat := 2*guard k n-1

def description (k r states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284CheckpointMarkedWorkspace.description k r (81+30*k+states)
    (Source284CheckpointRestored.postTable k continuation)

def postCost (k : Nat) (w : List Bool) : Nat :=
  Source284EraseZeroBlock.cost (shortZeros k w.length) (w++[false]).length+
  Source284EraseZeroBlock.cost (2*previous k w.length) (w++[false]).length+
  Source284EraseTokenHistory.cost k (base w.length) (base w.length) (w++[false]).length+
  (count k w.length+1)*(4*(w++[false]).length+7)

def totalCost (k r : Nat) (w : List Bool) : Nat :=
  Source284CheckpointMarkedWorkspace.totalCost k r w+postCost k w

theorem guard_positive (k n : Nat) : 1 ≤ guard k n := by
  have h := Source284CheckpointGrowth.checkpoint_blocks k n
  omega

theorem short_form (k n certificate : Nat) :
    shortHistory k n certificate = 2^(shortZeros k n+1)*
      (2*Source284UnaryPairScanner.pairTape (List.replicate (previous k n) false)
        (historyAfter k (base n) (base n) (2*certificate+1))+1) := by
  unfold shortHistory shortZeros
  have h := guard_positive k n
  have he : 2*guard k n-1+1 = 2*guard k n := by omega
  rw [he]

theorem restored_count (k n : Nat) :
    Source284EraseTokenHistory.cells k (base n) (base n)+(2*previous k n+2)+
      (shortZeros k n+2)+1 = count k n := by
  have h := Source284CheckpointRestored.mark_count k n
  have hg := guard_positive k n
  unfold shortZeros
  omega

/-- The paid post-processing consumes only the guard's counter, restores
exactly the original gap, and leaves the separate workspace counter untouched. -/
theorem source_then (k r states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description k r states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost k r w+fuel) =
    toSource (shiftConfig (1363+317*k+317*r) (run continuation
      ⟨2^(count k w.length+1)*(2*certificate+1),
        2*flipped (w++[false]) (higher k r w.length suffix),some 0⟩ fuel)) := by
  have hp := Source284CheckpointRestored.post_closed k states continuation hn hv
  have h := Source284CheckpointMarkedWorkspace.source_then k r (81+30*k+states)
    (Source284CheckpointRestored.postTable k continuation) w certificate suffix (postCost k w+fuel) (by omega) hp
  have ht : totalCost k r w+fuel = Source284CheckpointMarkedWorkspace.totalCost k r w+(postCost k w+fuel) := by
    simp [totalCost]; omega
  rw [ht]
  change Source284Relative.run (Source284CheckpointMarkedWorkspace.description k r _
    (Source284CheckpointRestored.postTable k continuation)) _ _ = _
  rw [h]
  unfold Source284CheckpointRestored.postTable postCost
  rw [short_form,Source284EraseTokenHistory.block_form]
  have ht2 : Source284EraseZeroBlock.cost (shortZeros k w.length) (w++[false]).length+
      Source284EraseZeroBlock.cost (2*previous k w.length) (w++[false]).length+
      Source284EraseTokenHistory.cost k (base w.length) (base w.length) (w++[false]).length+
      (count k w.length+1)*(4*(w++[false]).length+7)+fuel =
      Source284EraseZeroBlock.cost (shortZeros k w.length) (w++[false]).length+
      (Source284EraseZeroBlock.cost (2*previous k w.length) (w++[false]).length+
      (Source284EraseTokenHistory.cost k (base w.length) (base w.length) (w++[false]).length+
      ((count k w.length+1)*(4*(w++[false]).length+7)+fuel))) := by omega
  rw [ht2,Source284EraseMarkedBlock.erase_then,Source284EraseMarkedBlock.erase_then,
    Source284EraseMarkedHistory.erase_then]
  repeat rw [Source284EraseMarkedHistory.marks_add]
  have hcounter : Source284CountedShift.counter 1 (higher k r w.length suffix) =
      marks 1 (2*higher k r w.length suffix) := by rfl
  rw [hcounter,Source284EraseMarkedHistory.marks_add,restored_count,
    Source284RestoredPolynomialRunway.marks_counter,Source284CountedShift.countdown_after]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  have hs : (1282+287*k+317*r)+30+30+30*k+14+1+6=1363+317*k+317*r := by omega
  rw [hs]

end Shared.Beeping.NPcoNP.Source284CheckpointMarkedRestored
