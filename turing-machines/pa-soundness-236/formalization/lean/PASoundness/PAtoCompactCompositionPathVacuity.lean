import PASoundness.PAtoCompactPartialCompositionOutputUnique
import PASoundness.CompactFreshen

/-! Capture-safe witness-name vacuity for the explicit premises of the
composition endpoint step. Its uniqueness clauses bind name 4, so raw name
absence is unavailable; bound names are freshened with literal K proof
transport. No path witness or graph existence is asserted here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCompositionPathVacuity
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPartialCompositionOutputUnique
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not

/-- Exact uniqueness, endpoint equality, target guard and selected new edge
used by the endpoint coverage step. -/
def premises : Formula := conj firstUnique (conj secondUnique
  (conj (.equal 2 10) (conj (.member 8 3) (graphFormula 17 10 12))))

private theorem premises_names_lt : ∀ v ∈ premises.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ premises.names.sup id at hm
  have hb : premises.names.sup id < 30 := by decide
  omega

private def freshPremises := freshen premises 30 premises_names_lt
private theorem fresh_no4 : 4 ∉ freshPremises.formula.names := by decide

/-- The premises may be generalized over query-path witness 4 because both
occurrences of 4 are bound by the selected uniqueness formulas. -/
def premises_vacuity : KDerivation (imp premises.encode (allCode 4 premises.encode)) :=
  compose freshPremises.equivalent.forward
    (compose (freshPremises.formula.vacuity 4 fresh_no4)
      (allCongr 4 freshPremises.equivalent.backward))

theorem premises_vacuity_certificate :
    theoremCode (certificate premises_vacuity) =
      imp premises.encode (allCode 4 premises.encode) :=
  certificate_correct premises_vacuity

end PASoundness.PAtoCompactCompositionPathVacuity

#print axioms PASoundness.PAtoCompactCompositionPathVacuity.premises_vacuity
#print axioms PASoundness.PAtoCompactCompositionPathVacuity.premises_vacuity_certificate
