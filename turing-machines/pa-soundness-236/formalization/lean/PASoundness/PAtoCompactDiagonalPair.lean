import PASoundness.PAtoCompactOrderIsomorphism

/-! Capture-safe K specialization of an individual represented Kuratowski
pair to equal endpoint variables. This does not construct a collection of
pairs, an identity graph, or a quotient interpretation. -/
set_option maxRecDepth 65536
namespace PASoundness.PAtoCompactDiagonalPair
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism

/-- A derivation of the fixed-name pair-existence formula specializes to a
pair with both endpoint values read from name 2. -/
def diagonal_from_pair
    (hpair : KDerivation (existsCode 19 (pairFormula 19 2 3).encode)) :
    KDerivation (existsCode 19 (pairFormula 19 2 2).encode) := by
  let f : CompactNamed.Formula := .ex 19 (pairFormula 19 2 3)
  have h := CompactNamed.universalInstance 3 2 f (by decide) (by decide) (by decide)
  have hrep : CompactNamed.replace 3 2 f = .ex 19 (pairFormula 19 2 2) := by decide
  have hi : KDerivation (imp (allCode 3 (existsCode 19 (pairFormula 19 2 3).encode))
      (existsCode 19 (pairFormula 19 2 2).encode)) := by
    rw [hrep] at h
    exact h
  exact .mp (.generalize 3 hpair) hi

theorem diagonal_from_pair_certificate
    (hpair : KDerivation (existsCode 19 (pairFormula 19 2 3).encode)) :
    theoremCode (certificate (diagonal_from_pair hpair)) =
      existsCode 19 (pairFormula 19 2 2).encode :=
  certificate_correct (diagonal_from_pair hpair)

end PASoundness.PAtoCompactDiagonalPair

#print axioms PASoundness.PAtoCompactDiagonalPair.diagonal_from_pair
#print axioms PASoundness.PAtoCompactDiagonalPair.diagonal_from_pair_certificate
