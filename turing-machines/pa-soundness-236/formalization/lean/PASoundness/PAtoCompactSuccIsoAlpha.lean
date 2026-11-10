import PASoundness.PAtoCompactCleanMatrixData
import PASoundness.PAtoCompactSuccCongruenceWitnessVacuity

/-! Capture-safe graph-binder alignment for the successor-isomorphism path.
This supplies K alpha conversions only: no clean graph, isomorphism witness,
quotient congruence, or PA proof transport is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccIsoAlpha
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactCleanMatrixData PASoundness.PAtoCompactSuccCongruenceData
open PASoundness.PAtoCompactSuccCongruenceWitnessVacuity

/-- The exact E body at its original graph and endpoint names. -/
def originalBody : Formula := namedBoth bijectionFormula orderFormula

/-- The exact E body after replacing endpoint names 0,1 by 7,8. -/
def targetBody : Formula := replace 1 8 (replace 0 7 originalBody)

/-- The target quotient relation, with endpoints at names 7 and 8. -/
def targetEquivalent : Formula := replace 1 8 (replace 0 7 equivalentFormula)

theorem original_shape : equivalentFormula = .ex 6 originalBody := rfl

theorem old_body_shape : replace 6 10 originalBody = oldMatrix10 := rfl

theorem target_shape : targetEquivalent = .ex 6 targetBody := by decide

theorem target_body_shape : replace 6 9 targetBody = newMatrixNamed := by decide

/-- Move E's bound original graph name from 6 to fresh name 10. -/
def old_graph_alpha : KDerivation
    (imp equivalentFormula.encode (existsCode 10 oldMatrix10.encode)) := by
  have h := (existentialAlpha 6 10 originalBody (by decide) (by decide) (by decide)).1
  rw [old_body_shape] at h
  rw [original_shape]
  exact h

/-- Rebind a supplied successor matrix from graph name 9 to E's graph binder
6, preserving the exact renamed endpoint labels 7 and 8. -/
def new_graph_alpha : KDerivation (imp (existsCode 9 newMatrix) targetEquivalent.encode) := by
  have h := (existentialAlpha 6 9 targetBody (by decide) (by decide) (by decide)).2
  rw [target_body_shape] at h
  rw [target_shape]
  simpa only [newMatrix_encode, Formula.encode] using h

theorem old_graph_alpha_certificate : theoremCode (certificate old_graph_alpha) =
    imp equivalentFormula.encode (existsCode 10 oldMatrix10.encode) :=
  certificate_correct old_graph_alpha

theorem new_graph_alpha_certificate : theoremCode (certificate new_graph_alpha) =
    imp (existsCode 9 newMatrix) targetEquivalent.encode := certificate_correct new_graph_alpha

end PASoundness.PAtoCompactSuccIsoAlpha

#print axioms PASoundness.PAtoCompactSuccIsoAlpha.old_graph_alpha
#print axioms PASoundness.PAtoCompactSuccIsoAlpha.new_graph_alpha
#print axioms PASoundness.PAtoCompactSuccIsoAlpha.old_graph_alpha_certificate
#print axioms PASoundness.PAtoCompactSuccIsoAlpha.new_graph_alpha_certificate
