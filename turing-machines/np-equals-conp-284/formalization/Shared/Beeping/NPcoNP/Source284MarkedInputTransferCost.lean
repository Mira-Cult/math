import Shared.Beeping.NPcoNP.Source284MarkedInputTransfer

/-! Explicit polynomial clock for the source-generated workspace transfer. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284MarkedInputTransferCost

open Shared.Beeping.NPcoNP.Source284CheckpointWorkspace
open Shared.Beeping.NPcoNP.Source284CheckpointMarkedWorkspace

noncomputable def countPolynomial (k r : Nat) : Polynomial Nat :=
  Source284EraseMarkedHistory.cellsPolynomial r (Source284CheckpointCost.extraOuterPolynomial k)
    (Source284CheckpointCost.extraInnerPolynomial k)+Source284CheckpointCost.zerosPolynomial k r+2

theorem countPolynomial_eval (k r n : Nat) : (countPolynomial k r).eval n = markCount k r n := by
  simp [countPolynomial,markCount,Source284EraseMarkedHistory.cellsPolynomial_eval,
    Source284CheckpointCost.extraOuter_eval,Source284CheckpointCost.extraInner_eval,
    Source284CheckpointCost.zeros_eval,Polynomial.eval_add]

noncomputable def transferPolynomial (k r : Nat) : Polynomial Nat :=
  let width := Source284CheckpointCost.widthPolynomial
  3+(8*width+13)+(countPolynomial k r+2)*(4*width+7)+2+(6*width+11)+(4*width+12)

theorem transfer_polynomial (k r : Nat) (input : List Bool) :
    Source284InputCounterTransfer.cost input (markCount k r input.length-1) ≤
      (transferPolynomial k r).eval input.length := by
  have hmul := Nat.mul_le_mul_right (4*(input++[false]).length+7)
    (show markCount k r input.length-1+2 ≤ markCount k r input.length+2 by omega)
  simp only [transferPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Source284CheckpointCost.width_eval,countPolynomial_eval]
  unfold Source284InputCounterTransfer.cost
  omega

noncomputable def totalPolynomial (k r : Nat) : Polynomial Nat :=
  Source284CheckpointMarkedReveal.costPolynomial k r+transferPolynomial k r

theorem total_polynomial (k r : Nat) (input witness : List Bool) (certificate : Nat)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k input.length)
      certificate = some witness) :
    Source284MarkedInputTransfer.totalCost k r input witness ≤ (totalPolynomial k r).eval input.length := by
  have hfirst := Source284CheckpointMarkedReveal.cost_polynomial k r input witness certificate hdec
  have hsecond := transfer_polynomial k r input
  simp only [totalPolynomial,Polynomial.eval_add,Source284MarkedInputTransfer.totalCost]
  omega

end Shared.Beeping.NPcoNP.Source284MarkedInputTransferCost
