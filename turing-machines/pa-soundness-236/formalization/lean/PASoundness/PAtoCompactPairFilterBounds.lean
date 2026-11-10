import PASoundness.PAtoCompactPairFilter

/-! Numeric freshness of the generated pair filter's witness name. -/
namespace PASoundness.PAtoCompactPairFilterBounds
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactPairFilter

/-- The generated filter variable exceeds all three names occurring in the
pair predicate and the filtered container name. -/
theorem pair_witness_bounds (x t a b : Nat) :
    x < pairWitness x t a b ∧ t < pairWitness x t a b ∧
    a < pairWitness x t a b ∧ b < pairWitness x t a b := by
  have hf := filterPredicate_bounds x t (pairPredicate t a b)
  have h₁ := Cantor.right_le_pair t a
  have h₂ := Cantor.right_le_pair t b
  have h₃ := Cantor.left_le_pair (equal t a) 1
  have h₄ := Cantor.left_le_pair (neg (equal t a)) (equal t b)
  have h₅ := Cantor.right_le_pair (neg (equal t a)) (equal t b)
  dsimp [pairWitness, pairPredicate, CompactDerivations.either,
    CompactProof.neg, CompactProof.equal, CompactProof.imp] at *
  omega

end PASoundness.PAtoCompactPairFilterBounds

#print axioms PASoundness.PAtoCompactPairFilterBounds.pair_witness_bounds
