import PASoundness.PAtoCompactCompositionSelectedImages
import PASoundness.PAtoCompactPartialCompositionBase
import PASoundness.PAtoCompactPointAdjoin
import PASoundness.PAtoCompactAdjunction
import PASoundness.CompactFreshen

/-! Capture-safe vacuity of the complete supplied-witness context for one
partial-composition successor. Every graph, pair, image and successor is an
explicit antecedent; this module establishes neither the new invariant nor
witness existence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCompositionSuppliedVacuity
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactCompositionSelectedImages PASoundness.PAtoCompactPartialCompositionBase
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactAdjunction
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Shared supplied-witness context, in order: first and second image,
successor-prefix graph, new pair, point-adjunction, and old invariant. -/
def suppliedPremises : Formula := namedBoth firstImageBody (namedBoth secondImageBody
  (namedBoth (namedSuccessor 10 13 15) (namedBoth (pairFormula 16 10 12)
    (namedBoth (namedAdjoin 9 16 17 18) partialComposition))))

private theorem premises_names_lt : ∀ v ∈ suppliedPremises.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ suppliedPremises.names.sup id at hm
  have hb : suppliedPremises.names.sup id < 30 := by decide
  omega

/-- All bound names are freshened above 30; the two queried names are absent. -/
def freshPremises := freshen suppliedPremises 30 premises_names_lt

theorem fresh_2 : 2 ∉ freshPremises.formula.names := by decide
theorem fresh_3 : 3 ∉ freshPremises.formula.names := by decide
theorem fresh_4 : 4 ∉ freshPremises.formula.names := by decide

/-- The original premise implies its quantification at any name fresh for the
freshened formula, via the finite bidirectional alpha-conversion proof. -/
def premises_vacuity (v : Nat) (fresh : v ∉ freshPremises.formula.names) :
    KDerivation (imp suppliedPremises.encode (allCode v suppliedPremises.encode)) :=
  compose freshPremises.equivalent.forward (compose (freshPremises.formula.vacuity v fresh)
    (allCongr v freshPremises.equivalent.backward))

def vacuity_2 : KDerivation
    (imp suppliedPremises.encode (allCode 2 suppliedPremises.encode)) := premises_vacuity 2 fresh_2

def vacuity_3 : KDerivation
    (imp suppliedPremises.encode (allCode 3 suppliedPremises.encode)) := premises_vacuity 3 fresh_3

def vacuity_4 : KDerivation
    (imp suppliedPremises.encode (allCode 4 suppliedPremises.encode)) := premises_vacuity 4 fresh_4

theorem vacuity_2_certificate : theoremCode (certificate vacuity_2) =
    imp suppliedPremises.encode (allCode 2 suppliedPremises.encode) := certificate_correct vacuity_2

theorem vacuity_3_certificate : theoremCode (certificate vacuity_3) =
    imp suppliedPremises.encode (allCode 3 suppliedPremises.encode) := certificate_correct vacuity_3

theorem vacuity_4_certificate : theoremCode (certificate vacuity_4) =
    imp suppliedPremises.encode (allCode 4 suppliedPremises.encode) := certificate_correct vacuity_4

end PASoundness.PAtoCompactCompositionSuppliedVacuity

#print axioms PASoundness.PAtoCompactCompositionSuppliedVacuity.vacuity_2
#print axioms PASoundness.PAtoCompactCompositionSuppliedVacuity.vacuity_3
#print axioms PASoundness.PAtoCompactCompositionSuppliedVacuity.vacuity_4
#print axioms PASoundness.PAtoCompactCompositionSuppliedVacuity.vacuity_2_certificate
#print axioms PASoundness.PAtoCompactCompositionSuppliedVacuity.vacuity_3_certificate
#print axioms PASoundness.PAtoCompactCompositionSuppliedVacuity.vacuity_4_certificate
