import Shared.Beeping.NPcoNP.Source284CheckpointMarkedRestored
import Shared.Beeping.NPcoNP.Source284CheckpointGuardVerifier

/-! Quantitative facts about the generated unary workspace counter and its
paid source clock. The later operation that moves the counter's space to the
witness side remains a separate source-table obligation. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284CheckpointMarkedBounds

open Shared.Beeping.NPcoNP.Source284CheckpointWorkspace
open Shared.Beeping.NPcoNP.Source284CheckpointMarkedWorkspace
open Shared.Beeping.NPcoNP.Source284ScratchMarkedLoop (marks)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)

theorem mark_count_large (k r n : Nat) : workspace k r n+1 ≤ markCount k r n-1 := by
  unfold markCount cleanupZeros
  omega

theorem higher_marks (k r n suffix : Nat) :
    higher k r n suffix = marks (markCount k r n-1) (blankTail k r n suffix) := by
  have hcount := mark_count_large k r n
  have he : markCount k r n = (markCount k r n-1)+1 := by omega
  have hm : marks (markCount k r n) (blankTail k r n suffix) =
      2*marks (markCount k r n-1) (blankTail k r n suffix)+1 := by
    conv_lhs => rw [he]
    exact Source284EraseMarkedBlock.marks_succ _ _
  unfold higher
  rw [hm]
  omega

theorem blank_tail_even (k r n suffix : Nat) : 2 ∣ blankTail k r n suffix := by
  unfold blankTail
  have hp : 2 ∣ 2^(workspace k r n+1) := by
    have h : 1 ≤ workspace k r n+1 := by omega
    simpa using Nat.pow_dvd_pow 2 h
  exact dvd_mul_of_dvd_left hp _

/-- After guard cleanup, this is an actual unary counter on tape, followed
by a zero delimiter and the remaining high suffix. -/
theorem higher_counter (k r n suffix : Nat) :
    higher k r n suffix = counter (markCount k r n-1) (blankTail k r n suffix/2) := by
  rw [higher_marks]
  have hd : 2*(blankTail k r n suffix/2)=blankTail k r n suffix :=
    Nat.mul_div_cancel' (blank_tail_even k r n suffix)
  conv_lhs => rw [← hd]
  exact Source284RestoredPolynomialRunway.marks_counter _ _

/-- For any polynomial demand in the actual comparator bound, one extra
fixed stage count suffices; the counter length is selected at runtime by the
same source table and no external integer is injected. -/
theorem counter_dominates_bound (k : Nat) (p : Polynomial Nat) :
    ∃ r : Nat, ∀ n, p.eval (Source284DynamicGuardSource.bound k n) ≤ markCount k r n-1 := by
  obtain ⟨r,hr⟩ := Source284CheckpointGuardVerifier.workspace_dominates_bound k p
  exact ⟨r,fun n => le_trans (hr n) (by have h := mark_count_large k r n; omega)⟩

noncomputable def costPolynomial (k r : Nat) : Polynomial Nat :=
  Source284CheckpointRestored.costPolynomial k r+
    12*Source284CheckpointCost.widthPolynomial+27

/-- Marking, the separator pass, and the compensating extension add a
charged linear term to the previous polynomial initializer bound. -/
theorem totalCost_polynomial (k r : Nat) (w : List Bool) :
    Source284CheckpointMarkedRestored.totalCost k r w ≤ (costPolynomial k r).eval w.length := by
  have hold := Source284CheckpointRestored.totalCost_polynomial k r w
  have hshort : Source284CheckpointMarkedRestored.shortZeros k w.length ≤ 2*guard k w.length := by
    unfold Source284CheckpointMarkedRestored.shortZeros
    omega
  have hmul := Nat.mul_le_mul_right (8*(w++[false]).length+11) (show
    Source284CheckpointMarkedRestored.shortZeros k w.length+1 ≤ 2*guard k w.length+1 by omega)
  have hpost : Source284CheckpointMarkedRestored.postCost k w ≤ Source284CheckpointRestored.postCost k w := by
    unfold Source284CheckpointMarkedRestored.postCost Source284CheckpointRestored.postCost
      Source284EraseZeroBlock.cost
    omega
  simp only [costPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Source284CheckpointCost.width_eval]
  unfold Source284CheckpointMarkedRestored.totalCost Source284CheckpointMarkedWorkspace.totalCost
  unfold Source284CheckpointRestored.totalCost at hold
  omega

end Shared.Beeping.NPcoNP.Source284CheckpointMarkedBounds
