import Shared.Beeping.NPcoNP.Source284CheckpointCost
import Shared.Beeping.NPcoNP.Source284RestoredPolynomialRunway

/-! Paid restoration of the certificate after independently sized guard and
input-side workspace generation. The marked cleanup removes exactly the old
checkpoint history, and its finite countdown restores the input frame. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284CheckpointRestored

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284CheckpointWorkspace
open Shared.Beeping.NPcoNP.Source284ProductIteration (historyAfter)
open Shared.Beeping.NPcoNP.Source284ScratchMarkedLoop (marks)
open Shared.Beeping.NPcoNP.Source284PolynomialMarkedCleanup (count)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

def postTable (k : Nat) (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284EraseMarkedBlock.table (Source284EraseMarkedBlock.table
    (Source284EraseMarkedHistory.table k (Source284CountedShift.table continuation)))

def description (k r states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284CheckpointWorkspace.description k r (81+30*k+states) (postTable k continuation)

def postCost (k : Nat) (w : List Bool) : Nat :=
  Source284EraseZeroBlock.cost (2*guard k w.length) (w++[false]).length+
  Source284EraseZeroBlock.cost (2*previous k w.length) (w++[false]).length+
  Source284EraseTokenHistory.cost k (base w.length) (base w.length) (w++[false]).length+
  (count k w.length+1)*(4*(w++[false]).length+7)

def totalCost (k r : Nat) (w : List Bool) : Nat :=
  Source284CheckpointWorkspace.totalCost k r w+postCost k w

theorem post_closed (k states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (81+30*k+states) (postTable k continuation) := by
  have hs := Source284CountedShift.closed states continuation hn hv
  have hh := Source284EraseMarkedHistory.closed k (21+states) (Source284CountedShift.table continuation) (by omega) hs
  have h1 := Source284EraseMarkedBlock.closed (30*k+(21+states))
    (Source284EraseMarkedHistory.table k (Source284CountedShift.table continuation)) (by omega) hh
  have h2 := Source284EraseMarkedBlock.closed (30+(30*k+(21+states)))
    (Source284EraseMarkedBlock.table (Source284EraseMarkedHistory.table k (Source284CountedShift.table continuation))) (by omega) h1
  simpa [postTable,show 30+(30+(30*k+(21+states)))=81+30*k+states by omega] using h2

theorem mark_count (k n : Nat) :
    (2*guard k n+2)+(2*previous k n+2)+
      Source284EraseTokenHistory.cells k (base n) (base n) = count k n := by
  simp [count,Source284PolynomialRunwayCleanup.zeros,Source284PositivePolynomialRunway.block,
    Source284CheckpointWorkspace.guard,previous,base]
  omega

/-- The complete fixed table restores the original delimited certificate,
retains the input frame, and transfers the checkpoint history to a paid
countdown. Its right suffix is the independently enlarged workspace less one
blank cell. -/
theorem source_then (k r states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description k r states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost k r w+fuel) =
    toSource (shiftConfig (1333+317*k+317*r) (run continuation
      ⟨2^(count k w.length+1)*(2*certificate+1),
        2*flipped (w++[false]) (retained k r w.length suffix/2),some 0⟩ fuel)) := by
  have hp := post_closed k states continuation hn hv
  have h := Source284CheckpointWorkspace.source_then k r (81+30*k+states)
    (postTable k continuation) w certificate suffix (postCost k w+fuel) (by omega) hp
  have ht : totalCost k r w+fuel = Source284CheckpointWorkspace.totalCost k r w+(postCost k w+fuel) := by
    simp [totalCost]; omega
  rw [ht]
  change Source284Relative.run (Source284CheckpointWorkspace.description k r _ (postTable k continuation)) _ _ = _
  rw [h]
  unfold postTable postCost checkpointHistory
  rw [Source284EraseTokenHistory.block_form,Source284EraseTokenHistory.block_form]
  have ht2 : Source284EraseZeroBlock.cost (2*guard k w.length) (w++[false]).length+
      Source284EraseZeroBlock.cost (2*previous k w.length) (w++[false]).length+
      Source284EraseTokenHistory.cost k (base w.length) (base w.length) (w++[false]).length+
      (count k w.length+1)*(4*(w++[false]).length+7)+fuel =
      Source284EraseZeroBlock.cost (2*guard k w.length) (w++[false]).length+
      (Source284EraseZeroBlock.cost (2*previous k w.length) (w++[false]).length+
      (Source284EraseTokenHistory.cost k (base w.length) (base w.length) (w++[false]).length+
      ((count k w.length+1)*(4*(w++[false]).length+7)+fuel))) := by omega
  rw [ht2,Source284EraseMarkedBlock.erase_then,Source284EraseMarkedBlock.erase_then,
    Source284EraseMarkedHistory.erase_then]
  repeat rw [Source284EraseMarkedHistory.marks_add]
  have hm : Source284EraseTokenHistory.cells k (base w.length) (base w.length)+
      (2*previous k w.length+2)+(2*guard k w.length+2) = count k w.length := by
    have hcount := mark_count k w.length
    omega
  rw [hm]
  have heven : 2 ∣ retained k r w.length suffix := by
    simpa using Source284CheckpointGrowth.retained_zero k r w.length suffix 1 (by omega)
  have hd : 2*(retained k r w.length suffix/2)=retained k r w.length suffix := by
    exact Nat.mul_div_cancel' heven
  have hcounter : marks (count k w.length) (retained k r w.length suffix) =
      Source284CountedShift.counter (count k w.length) (retained k r w.length suffix/2) := by
    conv_lhs => rw [← hd]
    exact Source284RestoredPolynomialRunway.marks_counter _ _
  rw [hcounter,Source284CountedShift.countdown_after]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  have hs : (1252+287*k+317*r)+30+30+30*k+14+1+6=1333+317*k+317*r := by omega
  rw [hs]

noncomputable def blockCostPolynomial (p : Polynomial Nat) : Polynomial Nat :=
  (2*p+1)*(8*Source284CheckpointCost.widthPolynomial+11)+
    (8*Source284CheckpointCost.widthPolynomial+13)

noncomputable def costPolynomial (k r : Nat) : Polynomial Nat :=
  Source284CheckpointCost.costPolynomial k r+
  blockCostPolynomial (Source284CheckpointCost.guardPolynomial k)+
  blockCostPolynomial (Source284CheckpointCost.previousPolynomial k)+
  Source284EraseTokenHistory.costPolynomial k Source284CheckpointCost.basePolynomial
    Source284CheckpointCost.basePolynomial Source284CheckpointCost.widthPolynomial+
  (Source284RestoredPolynomialRunway.countPolynomial k+1)*
    (4*Source284CheckpointCost.widthPolynomial+7)

theorem totalCost_polynomial (k r : Nat) (w : List Bool) :
    totalCost k r w ≤ (costPolynomial k r).eval w.length := by
  have h := Source284CheckpointCost.totalCost_polynomial k r w
  have hh := Source284EraseTokenHistory.costPolynomial_eval k w.length
    Source284CheckpointCost.basePolynomial Source284CheckpointCost.basePolynomial
    Source284CheckpointCost.widthPolynomial
  rw [Source284CheckpointCost.base_eval,Source284CheckpointCost.width_eval] at hh
  simp only [costPolynomial,blockCostPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_one,Source284CheckpointCost.guard_eval,
    Source284CheckpointCost.previous_eval,Source284CheckpointCost.width_eval,
    Source284RestoredPolynomialRunway.countPolynomial_eval,hh]
  simp only [totalCost,postCost,Source284EraseZeroBlock.cost] at *
  omega

end Shared.Beeping.NPcoNP.Source284CheckpointRestored
