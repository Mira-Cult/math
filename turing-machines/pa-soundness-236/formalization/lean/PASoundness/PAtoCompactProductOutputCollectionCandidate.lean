import PASoundness.PAtoCompactProductOutputInsideClosed

/-! Candidate-prefix transported-product graph collection, using the proved
inside and outside successor constructions. Source product and output
bijection matrices and the candidate prefix remain explicit. This guarded
path invariant is not yet the target product-matrix theorem. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputCollectionCandidate

open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactProductOutputPartialBase PASoundness.PAtoCompactProductOutputInductionFixture
open PASoundness.PAtoCompactProductOutputCollectionInsideConditional PASoundness.PAtoCompactProductOutputInsideClosed

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Construct one represented graph satisfying the guarded path invariant
on candidate prefix 70, conditional on the two literal matrix hypotheses. -/
noncomputable def candidate_collection : KDerivation (imp assumptions.encode (imp candidatePrefix
    (existsCode 58 (replace 59 70 partialInvariant).encode))) :=
  prefix_collection_of_inside inside_step

theorem candidate_collection_certificate : theoremCode (certificate candidate_collection) =
    imp assumptions.encode (imp candidatePrefix
      (existsCode 58 (replace 59 70 partialInvariant).encode)) := certificate_correct _

end PASoundness.PAtoCompactProductOutputCollectionCandidate

#print axioms PASoundness.PAtoCompactProductOutputCollectionCandidate.candidate_collection
#print axioms PASoundness.PAtoCompactProductOutputCollectionCandidate.candidate_collection_certificate
