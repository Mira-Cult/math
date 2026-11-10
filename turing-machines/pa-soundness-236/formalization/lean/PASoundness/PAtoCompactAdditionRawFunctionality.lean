import PASoundness.PAtoCompactAdditionRawOutputEquivalence
import PASoundness.PAtoCompactCommonSourceSpanEquivalence

/-! Present the guarded raw-addition result using the existing ordinal
equivalence formula. The output graph binder is alpha-renamed explicitly. -/
namespace PASoundness.PAtoCompactAdditionRawFunctionality

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactConditionalTransitivityMatrix
open PASoundness.PAtoCompactCommonSourceSpanEquivalence

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def targetBody : Formula := replace 1 8 sourceMatrix
private theorem target_body_shape : replace 6 9 targetBody =
    PASoundness.PAtoCompactSeededSpanConditionalMatrix.targetMatrix := by
  symm
  exact PASoundness.PAtoCompactSeededSpanConditionalMatrix.target_matrix_exact

/-- Under the displayed candidate and raw-addition guard, the two actual
results satisfy the existing literal isomorphism relation. -/
def raw_addition_functionality : KDerivation
    (imp PASoundness.PAtoCompactAdditionRawOutputEquivalence.guard.encode targetEquivalent.encode) := by
  have halpha := (existentialAlpha 6 9 targetBody (by decide) (by decide) (by decide)).2
  rw [target_body_shape] at halpha
  have htarget : targetEquivalent.encode = existsCode 6 targetBody.encode := rfl
  rw [htarget]
  exact compose PASoundness.PAtoCompactAdditionRawOutputEquivalence.raw_addition_outputs_equivalent halpha

theorem raw_addition_functionality_certificate : theoremCode (certificate raw_addition_functionality) =
    imp PASoundness.PAtoCompactAdditionRawOutputEquivalence.guard.encode targetEquivalent.encode :=
  certificate_correct raw_addition_functionality

end PASoundness.PAtoCompactAdditionRawFunctionality

#print axioms PASoundness.PAtoCompactAdditionRawFunctionality.raw_addition_functionality
#print axioms PASoundness.PAtoCompactAdditionRawFunctionality.raw_addition_functionality_certificate
