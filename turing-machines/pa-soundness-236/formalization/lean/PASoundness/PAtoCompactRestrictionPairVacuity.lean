import PASoundness.PAtoCompactKuratowskiSyntax
import PASoundness.CompactDerivations

/-! Witness-label vacuity for a graph's pair and first endpoint membership. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictionPairVacuity
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSingleton
open PASoundness.PAtoCompactUnorderedPair PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactKuratowskiSyntax
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Vacuity of a fresh label in the literal pair witness. -/
def pair_vacuity (u v q : Nat)
    (h19 : q ≠ 19) (hu : q ≠ u) (hv : q ≠ v)
    (h20 : q ≠ 20) (h21 : q ≠ 21) (h22 : q ≠ 22) :
    KDerivation (imp (pairFormula 19 u v).encode
      (allCode q (pairFormula 19 u v).encode)) := by
  have fresh : q ∉ (pairFormula 19 u v).names := by
    rw [pair_formula_named]
    simp [namedSingleton, namedPair, namedBoth, namedEither, Formula.names,
      h19, hu, hv, h20, h21, h22]
  exact (pairFormula 19 u v).vacuity q fresh

/-- The first endpoint membership does not depend on witness label 26 when
its containing-set label differs from 26. -/
def first_member_vacuity_26 (x : Nat) (hx : 26 ≠ x) :
    KDerivation (imp (member x 25) (allCode 26 (member x 25))) :=
  membershipVacuity x 25 26 hx (by decide)

end PASoundness.PAtoCompactRestrictionPairVacuity

#print axioms PASoundness.PAtoCompactRestrictionPairVacuity.pair_vacuity
#print axioms PASoundness.PAtoCompactRestrictionPairVacuity.first_member_vacuity_26
