import PASoundness.PAtoCompactProductMatchInsideClosed

/-! Candidate-guarded collection of one represented product-match graph
from the two supplied product matrices and two supplied factor-bijection
matrices. The intended result is the guarded graph invariant only; this does
not establish reverse matching, order preservation, or multiplication
congruence. -/
namespace PASoundness.PAtoCompactProductMatchCollectionCandidate

open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactProductMatchPartialBase
open PASoundness.PAtoCompactProductMatchCollectionInsideConditional
open PASoundness.PAtoCompactProductMatchInsideClosed

/-- Under the explicit source-candidate and four graph-matrix hypotheses,
construct a graph whose guarded source/target edges are exactly the matching
paths. No global product-isomorphism claim is made. -/
def source_collection : KDerivation
    (imp assumptions.encode (imp (candidateCode 2 81 77 78 72 64 73 59 75)
      (existsCode 58 (replace 59 2 partialMatch).encode))) :=
  source_collection_of_inside inside_step

theorem source_collection_certificate : theoremCode (certificate source_collection) =
    imp assumptions.encode (imp (candidateCode 2 81 77 78 72 64 73 59 75)
      (existsCode 58 (replace 59 2 partialMatch).encode)) := certificate_correct _

end PASoundness.PAtoCompactProductMatchCollectionCandidate

#print axioms PASoundness.PAtoCompactProductMatchCollectionCandidate.source_collection
#print axioms PASoundness.PAtoCompactProductMatchCollectionCandidate.source_collection_certificate
