import PASoundness.PAtoCompactDiagonalReflexiveMatrixTransport

/-! A bound graph name can be generalized out of the exact reflexive candidate
formula. Alpha conversion through fresh name 40 supplies the needed vacuity;
this does not establish any graph, isomorphism, or PA interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalReflexiveVacuity
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactDiagonalReflexiveMatrixTransport

def reflexiveMatrix : CompactNamed.Formula :=
  CompactNamed.replace 1 30 (CompactNamed.replace 0 30 (namedBoth bijectionFormula orderFormula))

def renamedReflexive : CompactNamed.Formula :=
  .ex 40 (CompactNamed.replace 6 40 reflexiveMatrix)

/-- The exact reflexive formula has graph binder 6 and the displayed matrix. -/
theorem reflexive_syntax : reflexive30 = .ex 6 reflexiveMatrix := by rfl

/-- Vacuity of graph name 6, proved by alpha-renaming the bound witness to 40,
generalizing there, and transporting back under the universal quantifier. -/
def reflexive_vacuity_6 : KDerivation (imp reflexive30.encode (allCode 6 reflexive30.encode)) := by
  have ha := CompactNamed.existentialAlpha 6 40 reflexiveMatrix (by decide) (by decide) (by decide)
  have h40 : 6 ∉ renamedReflexive.names := by decide
  have hv := renamedReflexive.vacuity 6 h40
  have h : KDerivation (imp (existsCode 6 reflexiveMatrix.encode)
      (allCode 6 (existsCode 6 reflexiveMatrix.encode))) :=
    compose ha.1 (compose hv (allCongr 6 ha.2))
  simpa only [reflexive_syntax, CompactNamed.Formula.encode] using h

theorem reflexive_vacuity_6_certificate : theoremCode (certificate reflexive_vacuity_6) =
    imp reflexive30.encode (allCode 6 reflexive30.encode) :=
  certificate_correct reflexive_vacuity_6

end PASoundness.PAtoCompactDiagonalReflexiveVacuity

#print axioms PASoundness.PAtoCompactDiagonalReflexiveVacuity.reflexive_vacuity_6
#print axioms PASoundness.PAtoCompactDiagonalReflexiveVacuity.reflexive_vacuity_6_certificate
