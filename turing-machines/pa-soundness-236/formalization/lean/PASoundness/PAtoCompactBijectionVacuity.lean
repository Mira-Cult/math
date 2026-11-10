import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactFreshen

/-! Vacuity for the exact proposed bijection formula at its bound name 3.
Freshening supplies explicit K proof equivalence; no semantic soundness or
graph-existence theorem is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactBijectionVacuity
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private theorem bijection_names_lt : ∀ v ∈ bijectionFormula.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ bijectionFormula.names.sup id at hm
  have hb : bijectionFormula.names.sup id < 30 := by decide
  omega

/-- Capture-safe freshening of the bijection's bound labels, starting above
all names in the original formula. -/
def freshBijection := freshen bijectionFormula 30 bijection_names_lt

private theorem fresh_bijection_avoids_three : 3 ∉ freshBijection.formula.names := by decide

/-- The exact bijection formula entails its universal closure at name 3.
Name 3 occurs bound in the original syntax; the proof first freshens those
binders, applies literal syntactic vacuity, then transports back using the
reverse K derivation. This does not construct a bijection or inverse. -/
def bijection_vacuity_three : KDerivation
    (imp bijectionFormula.encode (allCode 3 bijectionFormula.encode)) :=
  compose freshBijection.equivalent.forward
    (compose (freshBijection.formula.vacuity 3 fresh_bijection_avoids_three)
      (allCongr 3 freshBijection.equivalent.backward))

theorem bijection_vacuity_three_certificate :
    theoremCode (certificate bijection_vacuity_three) =
      imp bijectionFormula.encode (allCode 3 bijectionFormula.encode) :=
  certificate_correct bijection_vacuity_three

end PASoundness.PAtoCompactBijectionVacuity

#print axioms PASoundness.PAtoCompactBijectionVacuity.bijection_vacuity_three
#print axioms PASoundness.PAtoCompactBijectionVacuity.bijection_vacuity_three_certificate
