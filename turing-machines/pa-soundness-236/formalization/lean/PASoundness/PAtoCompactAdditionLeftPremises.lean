import PASoundness.PAtoCompactAdditionLeftPointClosed
import PASoundness.PAtoCompactSuccBijectionPremisesAtTwo
import PASoundness.CompactFreshen

/-! Exact common assumptions for the source clause of the unequal-top graph.
Vacuity at source name 2 requires freshening the old bijection's bound names.
These are literal K derivations; no graph existence or bijection is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionLeftPremises
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactAdditionSuccessorGraphClean
open PASoundness.PAtoCompactAdditionOldSourceClosed
open PASoundness.PAtoCompactSuccBijectionPremisesAtTwo
open PASoundness.PAtoCompactSuccessorInjective PASoundness.PAtoCompactTransitiveClosure
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def premisesCode : Nat := both oldBijection.encode (both oldClean.encode
  (both (adjoinCode 6 11 9 16) (both (pairFormula 11 31 32).encode
    (both (adjoinCode 34 32 40 41) (successorCode 31 38 39)))))

private theorem names_lt : ∀ v ∈ oldBijection.names, v < 60 := by
  intro v hv
  have h := Finset.le_sup (f := id) hv
  change v ≤ oldBijection.names.sup id at h
  have h' : oldBijection.names.sup id < 60 := by decide
  omega
private def freshBijection := freshen oldBijection 60 names_lt
private theorem fresh2 : 2 ∉ freshBijection.formula.names := by decide

/-- Freshening the bound labels establishes vacuity at the point name 2. -/
def bijection_vacuity : KDerivation (imp oldBijection.encode (allCode 2 oldBijection.encode)) :=
  compose freshBijection.equivalent.forward
    (compose (freshBijection.formula.vacuity 2 fresh2) (allCongr 2 freshBijection.equivalent.backward))

/-- The exact six supplied premises are vacuous at source name 2. -/
def premises_vacuity : KDerivation (imp premisesCode (allCode 2 premisesCode)) := by
  let A : Formula := namedAdjoin 6 11 9 16
  let T : Formula := namedAdjoin 34 32 40 41
  have hc : KDerivation (imp oldClean.encode (allCode 2 oldClean.encode)) := oldClean.vacuity 2 (by decide)
  have ha : KDerivation (imp (adjoinCode 6 11 9 16) (allCode 2 (adjoinCode 6 11 9 16))) := by
    have h := A.vacuity 2 (by decide)
    simpa [A,namedAdjoin,namedBoth,namedEither,Formula.encode,adjoinCode,both,neg,either] using h
  have hp : KDerivation (imp (pairFormula 11 31 32).encode (allCode 2 (pairFormula 11 31 32).encode)) :=
    (pairFormula 11 31 32).vacuity 2 (by decide)
  have ht : KDerivation (imp (adjoinCode 34 32 40 41) (allCode 2 (adjoinCode 34 32 40 41))) := by
    have h := T.vacuity 2 (by decide)
    simpa [T,namedAdjoin,namedBoth,namedEither,Formula.encode,adjoinCode,both,neg,either] using h
  have hs : KDerivation (imp (successorCode 31 38 39) (allCode 2 (successorCode 31 38 39))) :=
    successor_vacuity 31 38 39 2 (by decide) (by decide) (by decide)
  unfold premisesCode
  exact conjunction_vacuity 2 _ _ bijection_vacuity
    (conjunction_vacuity 2 _ _ hc (conjunction_vacuity 2 _ _ ha
      (conjunction_vacuity 2 _ _ hp (conjunction_vacuity 2 _ _ ht hs))))

theorem premises_vacuity_certificate : theoremCode (certificate premises_vacuity) =
    imp premisesCode (allCode 2 premisesCode) := certificate_correct premises_vacuity
end PASoundness.PAtoCompactAdditionLeftPremises
#print axioms PASoundness.PAtoCompactAdditionLeftPremises.bijection_vacuity
#print axioms PASoundness.PAtoCompactAdditionLeftPremises.premises_vacuity
#print axioms PASoundness.PAtoCompactAdditionLeftPremises.premises_vacuity_certificate
