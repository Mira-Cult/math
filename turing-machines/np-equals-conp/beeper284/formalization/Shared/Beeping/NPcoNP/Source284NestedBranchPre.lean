import Shared.Beeping.NPcoNP.Source284NestedBothBranches

/-! Exact pre-exit configurations for both finite branch returns. These
lemmas expose the rows that a future loop may redirect without changing the
preceding finite computation. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284NestedBranchPre

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchScanner (push)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

theorem nested_return_pre (continuation : Nat → Bool → Row) (m outer stream : Nat) :
    run (Source284NestedReturn.table continuation)
      ⟨outer,4*push (2*stream+1) (List.replicate m false),some 0⟩ (2*m+3) =
    ⟨2*stream,pairTape (List.replicate m false) outer,some 9⟩ := by
  have ht : 2*m+3 = 2+(2*m+1) := by omega
  rw [ht,Source284ScratchScanner.run_add]
  have hp : run (Source284NestedReturn.table continuation)
      ⟨outer,4*push (2*stream+1) (List.replicate m false),some 0⟩ 2 =
      shiftConfig 2 ⟨4*outer+2,push (2*stream+1) (List.replicate m false),some 0⟩ := by
    simp [run,step,Source284NestedReturn.table,shiftConfig,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega
  rw [hp,Source284NestedReturn.relocated_run]
  have he : 2*m+1 = (2*m)+1 := by omega
  rw [he,Source284NestedReturn.return_jump,← he]
  rw [Source284UnaryPairScanner.push_zeros,Source284ScratchScanner.run_add,
    Source284UnaryClear.back_pairs]
  have hz : 4^m*(4*outer+2) = pairTape (List.replicate m false) outer := by
    rw [show 4^m = 2^(2*m) by rw [Nat.pow_mul],
      ← Source284ScratchSentinel.unaryPairs_stack,← Source284UnaryPairScanner.zero_pairTape]
  simp [run,step,Source284UnaryClear.table,shiftConfig,bit,Nat.testBit_zero,Nat.add_mod,hz] <;> omega

theorem dual_return_pre (continuation : Nat → Bool → Row) (mode m outer stream : Nat) (hm : mode < 2) :
    run (Source284DualReturn.table continuation)
      ⟨outer,4*push (2*stream+1) (List.replicate m false),some mode⟩ (2*m+5) =
    ⟨2*stream,pairTape (List.replicate m false) outer,some (Source284DualReturn.offset mode+9)⟩ := by
  have ht : 2*m+5 = 2+(2*m+3) := by omega
  rw [ht,Source284ScratchScanner.run_add,Source284DualReturn.enter _ _ _ _ hm]
  have hv : Valid 11 ⟨outer,4*push (2*stream+1) (List.replicate m false),some 0⟩ := by
    intro q hq; simp at hq; omega
  rw [Source284DualReturn.copy_run _ _ _ hm hv]
  change shiftConfig (Source284DualReturn.offset mode)
    (run (Source284NestedReturn.table Source284DualReturn.sink)
      ⟨outer,4*push (2*stream+1) (List.replicate m false),some 0⟩ _) = _
  rw [nested_return_pre]
  simp [shiftConfig]

theorem mark_pre (continuation : Nat → Bool → Row) (m k : Nat) (rest : List Bool)
    (certificate stream : Nat) :
    run (Source284NestedBothBranches.table continuation)
      ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true ++ false::rest) certificate),
        2*stream,some 0⟩ (4*m+4*k+13) =
    ⟨2*stream,pairTape (List.replicate m false) (pairTape (List.replicate k true ++ true::rest) certificate),
      some 30⟩ := by
  have ht : 4*m+4*k+13 = (2*(List.replicate m false).length+4*k+8)+(2*m+5) := by simp; omega
  rw [ht,Source284ScratchScanner.run_add]
  unfold Source284NestedBothBranches.table
  rw [Source284NestedMarker.mark_outer]
  change run (Source284NestedMarker.table (Source284DualReturn.table continuation))
    (shiftConfig 17 ⟨pairTape (List.replicate k true ++ true::rest) certificate,
      4*push (2*stream+1) (List.replicate m false),some 0⟩) _ = _
  rw [Source284NestedMarkRestore.continuation_run,dual_return_pre _ 0 m _ _ (by omega)]
  rfl

theorem exhausted_pre (continuation : Nat → Bool → Row) (m k certificate stream : Nat) :
    run (Source284NestedBothBranches.table continuation)
      ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true) certificate),
        2*stream,some 0⟩ (4*m+4*k+13) =
    ⟨2*stream,pairTape (List.replicate m false) (pairTape (List.replicate k true) certificate),some 41⟩ := by
  have ht : 4*m+4*k+13 = (2*(List.replicate m false).length+4*k+8)+(2*m+5) := by simp; omega
  rw [ht,Source284ScratchScanner.run_add]
  unfold Source284NestedBothBranches.table
  rw [Source284NestedMarker.outer_exhausted]
  change run (Source284NestedMarker.table (Source284DualReturn.table continuation))
    (shiftConfig 17 ⟨pairTape (List.replicate k true) certificate,
      4*push (2*stream+1) (List.replicate m false),some 1⟩) _ = _
  rw [Source284NestedMarkRestore.continuation_run,dual_return_pre _ 1 m _ _ (by omega)]
  rfl

end Shared.Beeping.NPcoNP.Source284NestedBranchPre
