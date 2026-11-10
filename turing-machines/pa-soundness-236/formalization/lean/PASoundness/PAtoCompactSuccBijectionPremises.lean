import PASoundness.PAtoCompactSuccCongruenceData
import PASoundness.PAtoCompactAdjunction

/-! A named conjunction of all explicitly supplied successor-congruence
hypotheses, and its capture-safe K vacuity at pointwise name 28. This states
no graph existence, isomorphism conclusion or quotient property. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccBijectionPremises
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactSuccCongruenceData

/-- Every premise is retained literally; no hidden graph or domain hypothesis. -/
def premisesCode : Nat := both oldMatrix (both cleanGraph
  (both sourceSuccessor (both targetSuccessor (both newPair (both newGraph
    (both sourceIrreflexive targetIrreflexive))))))

/-- A named representation with name 28 absent from all its free and bound
labels, for direct derivation of vacuity. -/
def premisesNamed : Formula := namedBoth (namedBoth bijectionFormula orderFormula)
  (namedBoth (.all 19 (.imp (.member 6 19) (edgePredicate 19 0 1)))
    (namedBoth (namedSuccessor 0 7 14)
      (namedBoth (namedSuccessor 1 8 15)
        (namedBoth (pairFormula 11 0 1)
          (namedBoth (namedAdjoin 6 11 9 16)
            (namedBoth (.imp (.member 0 0) .bottom) (.imp (.member 1 1) .bottom)))))))

/-- This is the exact literal code of the eight displayed premises. -/
theorem premises_encode : premisesNamed.encode = premisesCode := by
  rfl

/-- Name 28 is absent even from internal binders, so the full conjunction
can be retained across generalization in the exact K calculus. -/
def premises_vacuity_28 : KDerivation (imp premisesCode (allCode 28 premisesCode)) := by
  have h := premisesNamed.vacuity 28 (by decide)
  simpa only [premises_encode] using h

theorem premises_vacuity_28_certificate :
    theoremCode (certificate premises_vacuity_28) = imp premisesCode (allCode 28 premisesCode) :=
  certificate_correct premises_vacuity_28

end PASoundness.PAtoCompactSuccBijectionPremises

#print axioms PASoundness.PAtoCompactSuccBijectionPremises.premises_encode
#print axioms PASoundness.PAtoCompactSuccBijectionPremises.premises_vacuity_28
#print axioms PASoundness.PAtoCompactSuccBijectionPremises.premises_vacuity_28_certificate
