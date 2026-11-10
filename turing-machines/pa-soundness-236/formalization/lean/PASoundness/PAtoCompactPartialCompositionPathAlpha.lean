import PASoundness.PAtoCompactConditionalTransitivityPoint
import PASoundness.CompactFreshen

/-! Literal K alpha conversion for the bounded middle witness in composition.
This does not assert that a composition graph exists or that the candidate
order-isomorphism relation is transitive. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionPathAlpha
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityPoint

/-- The composition path used inside the partial-prefix invariant, with
middle witness at name 4. -/
def pathBodyFour : Formula := namedBoth (.member 1 4)
  (namedBoth (graphFormula 6 2 4) (graphFormula 7 4 3))

def pathFour : Formula := .ex 4 pathBodyFour

/-- Fresh-name substitution gives exactly the separately defined target path
body, with name 10 as its existential witness. -/
theorem path_body_rename : replace 4 10 pathBodyFour = pathBody := by decide

/-- Explicit finite K derivations in both directions, plus standard semantic
agreement, for replacing the middle witness binder 4 by the fresh name 10. -/
def path_alpha : ProofEquiv pathFour path := by
  have h := ProofEquiv.alphaExists 4 10 pathBodyFour (by decide) (by decide) (by decide)
  rw [path_body_rename] at h
  exact h

def path_to_target : KDerivation (imp pathFour.encode path.encode) := path_alpha.forward
def path_from_target : KDerivation (imp path.encode pathFour.encode) := path_alpha.backward

theorem path_to_target_certificate : theoremCode (certificate path_to_target) =
    imp pathFour.encode path.encode := certificate_correct path_to_target

theorem path_from_target_certificate : theoremCode (certificate path_from_target) =
    imp path.encode pathFour.encode := certificate_correct path_from_target

end PASoundness.PAtoCompactPartialCompositionPathAlpha

#print axioms PASoundness.PAtoCompactPartialCompositionPathAlpha.path_to_target
#print axioms PASoundness.PAtoCompactPartialCompositionPathAlpha.path_from_target
