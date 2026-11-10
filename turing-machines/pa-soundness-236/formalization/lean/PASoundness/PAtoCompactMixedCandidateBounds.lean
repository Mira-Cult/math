import PASoundness.PAtoCompactMixedCandidateAlignment
import PASoundness.PAtoCompactPairFilterBounds

/-! A numeric lower bound for the fresh names selected by the mixed-order
pair filter. This is syntactic allocation evidence, not a theorem of K or a
semantic candidate argument. -/
namespace PASoundness.PAtoCompactMixedCandidateBounds

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactPairFilter
open PASoundness.PAtoCompactLocalPairFresh

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The encoded pair-filter witness exceeds four times its test label. -/
theorem pair_witness_test_quad (x t a b : Nat) :
    4 * t < pairWitness x t a b := by
  have hfilter : pairPredicate t a b < pairWitness x t a b :=
    (filterPredicate_bounds x t (pairPredicate t a b)).2.2
  have hp := Cantor.left_le_pair t a
  have hn := Cantor.left_le_pair (equal t a) 1
  have he := Cantor.left_le_pair (neg (equal t a)) (equal t b)
  dsimp only [pairPredicate,CompactDerivations.either,CompactProof.neg,
    CompactProof.imp,CompactProof.equal] at hfilter hn he
  omega

end PASoundness.PAtoCompactMixedCandidateBounds

#print axioms PASoundness.PAtoCompactMixedCandidateBounds.pair_witness_test_quad
