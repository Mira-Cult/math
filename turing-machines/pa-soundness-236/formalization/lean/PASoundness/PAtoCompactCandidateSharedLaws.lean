import PASoundness.PAtoCompactCandidateBinderBridge
import PASoundness.PAtoCompactCandidateSymmetryObject

/-! Reflexivity and symmetry at one object name under one exact candidate
predicate. Symmetry is supplied as explicit K proof data, so this module does
not conceal its inverse-graph dependencies. No transitivity or PA transport is
asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateSharedLaws
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactOrderIsoSwap PASoundness.PAtoCompactCandidateSymmetryObject
open PASoundness.PAtoCompactCandidateBinderBridge PASoundness.PAtoCompactCandidateReflexiveObject

/-- The reflexive formula and forward isomorphism use the very same named
relation after placing object 8 in the remaining argument. -/
theorem reflexive_agrees_with_forward : reflexive8 =
    CompactNamed.replace 1 8 equivalentEightOne := by decide

/-- One literal candidate hypothesis yields reflexivity and the supplied
symmetry proof, both at the same object name 8. -/
def shared_laws
    (symmetry : KDerivation (imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp equivalentFormula.encode reverseEquivalent.encode))) :
    KDerivation (imp (candidateCode 8 37 32 33 34 30 35 10 36)
      (both reflexive8.encode (imp equivalentEightOne.encode equivalentOneEight.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  let D := candidateCode 8 37 32 33 34 30 35 10 36
  let Γ := [D]
  have hd : Context Γ D := Context.head [] D
  have hr := Context.mp hd (.closed reflexivity_under_symmetry_candidate)
  have hs := Context.mp hd (.closed (specialize_symmetry symmetry))
  exact Context.conjunctionIntro hr hs

theorem shared_laws_certificate
    (symmetry : KDerivation (imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp equivalentFormula.encode reverseEquivalent.encode))) :
    theoremCode (certificate (shared_laws symmetry)) =
      imp (candidateCode 8 37 32 33 34 30 35 10 36)
        (both reflexive8.encode (imp equivalentEightOne.encode equivalentOneEight.encode)) :=
  certificate_correct (shared_laws symmetry)

end PASoundness.PAtoCompactCandidateSharedLaws

#print axioms PASoundness.PAtoCompactCandidateSharedLaws.shared_laws
#print axioms PASoundness.PAtoCompactCandidateSharedLaws.shared_laws_certificate
