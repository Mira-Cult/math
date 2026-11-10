import PASoundness.PAtoCompactProductOutputOutsidePath

/-! Lift the outside-prefix body comparison through the same source-output
existential. This is not yet the global represented graph step. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputOutsidePathLift

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactProductOutputOutsidePath PASoundness.PAtoCompactProductOutputPartialBase

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def oldPath : Formula := .ex 32 oldBody
def nextPath : Formula := .ex 32 nextBody
theorem next_path_shape : nextPath = pathAt := by decide

def outside_path_equiv : KDerivation (imp guard.encode
    (both (imp nextPath.encode oldPath.encode) (imp oldPath.encode nextPath.encode))) := by
  have hf : KDerivation (imp guard.encode (imp nextBody.encode oldBody.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    have hg : Context [guard.encode] guard.encode := .head _ _
    exact Context.conjunctionLeft (Context.mp hg (.closed outside_body_equiv))
  have hb : KDerivation (imp guard.encode (imp oldBody.encode nextBody.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    have hg : Context [guard.encode] guard.encode := .head _ _
    exact Context.conjunctionRight (Context.mp hg (.closed outside_body_equiv))
  have hF := conditionalExistsCongr 32 (guard.vacuity 32 (by decide)) hf
  have hB := conditionalExistsCongr 32 (guard.vacuity 32 (by decide)) hb
  apply Context.closeEmpty
  apply Context.deduction
  have hg : Context [guard.encode] guard.encode := .head _ _
  have h := Context.conjunctionIntro (Context.mp hg (.closed hF)) (Context.mp hg (.closed hB))
  simpa [oldPath, nextPath, Formula.encode] using h

theorem outside_path_equiv_certificate : theoremCode (certificate outside_path_equiv) =
    imp guard.encode (both (imp nextPath.encode oldPath.encode) (imp oldPath.encode nextPath.encode)) :=
  certificate_correct _

end PASoundness.PAtoCompactProductOutputOutsidePathLift

#print axioms PASoundness.PAtoCompactProductOutputOutsidePathLift.outside_path_equiv
#print axioms PASoundness.PAtoCompactProductOutputOutsidePathLift.outside_path_equiv_certificate
