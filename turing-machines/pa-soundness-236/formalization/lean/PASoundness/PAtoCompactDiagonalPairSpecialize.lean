import PASoundness.PAtoCompactDiagonalPairClosed

/-! Capture-safe K specialization and alpha conversion for one diagonal
Kuratowski pair. This does not construct an identity graph or collection. -/
set_option maxRecDepth 65536
namespace PASoundness.PAtoCompactDiagonalPairSpecialize
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactDiagonalPairClosed

/-- A fixed-name diagonal pair-existence derivation specializes its free
endpoint name 2 to name 0 and renames the output binder 19 to 8. -/
def specialize_diagonal_pair
    (hpair : KDerivation (existsCode 19 (pairFormula 19 2 2).encode)) :
    KDerivation (existsCode 8 (pairFormula 8 0 0).encode) := by
  let f : Formula := .ex 19 (pairFormula 19 2 2)
  have h := CompactNamed.universalInstance 2 0 f (by decide) (by decide) (by decide)
  have hrep : CompactNamed.replace 2 0 f = .ex 19 (pairFormula 19 0 0) := by decide
  have hi : KDerivation (imp (allCode 2 (existsCode 19 (pairFormula 19 2 2).encode))
      (existsCode 19 (pairFormula 19 0 0).encode)) := by
    rw [hrep] at h
    exact h
  have hzero : KDerivation (existsCode 19 (pairFormula 19 0 0).encode) :=
    .mp (.generalize 2 hpair) hi
  have halpha := (CompactNamed.existentialAlpha 19 8 (pairFormula 19 0 0)
    (by decide) (by decide) (by decide)).1
  have hrename : CompactNamed.replace 19 8 (pairFormula 19 0 0) = pairFormula 8 0 0 := by decide
  rw [hrename] at halpha
  exact .mp hzero halpha

/-- K constructs the individual diagonal pair at the fixed target labels. -/
def diagonal_pair_exists : KDerivation (existsCode 8 (pairFormula 8 0 0).encode) :=
  specialize_diagonal_pair PAtoCompactDiagonalPairClosed.diagonal_pair_exists

theorem diagonal_pair_exists_certificate : theoremCode (certificate diagonal_pair_exists) =
    existsCode 8 (pairFormula 8 0 0).encode := certificate_correct diagonal_pair_exists

end PASoundness.PAtoCompactDiagonalPairSpecialize

#print axioms PASoundness.PAtoCompactDiagonalPairSpecialize.diagonal_pair_exists
#print axioms PASoundness.PAtoCompactDiagonalPairSpecialize.diagonal_pair_exists_certificate
