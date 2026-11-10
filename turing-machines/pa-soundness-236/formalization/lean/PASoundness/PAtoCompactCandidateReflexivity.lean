import PASoundness.PAtoCompactDiagonalCandidateInduction
import PASoundness.PAtoCompactDiagonalIsomorphism
import PASoundness.PAtoCompactDiagonalReflexiveAlign

/-! Candidate-relative reflexivity of the proposed order-isomorphism relation,
as finite literal K proof data. The exact candidate and reflexive named
formula retain name 30; the candidate's bound name 0 is never substituted.
This proves neither symmetry nor transitivity, congruence, arithmetic
operations, PA proof transport, or the final soundness equivalence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateReflexivity
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactDiagonalCandidateInduction
open PASoundness.PAtoCompactDiagonalIsomorphism PASoundness.PAtoCompactDiagonalReflexiveAlign
open PASoundness.PAtoCompactDiagonalReflexiveMatrixTransport

/-- Every input satisfying the exact fixed-name candidate predicate is related
to itself by the proposed relational order-isomorphism formula. -/
def candidate_reflexive : KDerivation
    (imp (candidateCode 30 41 37 38 32 0 31 34 35) reflexive30.encode) :=
  compose candidate_diagonal_graph_exists
    (invariant_exists_to_reflexive diagonal_isomorphism_matrix)

theorem candidate_reflexive_certificate : theoremCode (certificate candidate_reflexive) =
    imp (candidateCode 30 41 37 38 32 0 31 34 35) reflexive30.encode :=
  certificate_correct candidate_reflexive

end PASoundness.PAtoCompactCandidateReflexivity

#print axioms PASoundness.PAtoCompactCandidateReflexivity.candidate_reflexive
#print axioms PASoundness.PAtoCompactCandidateReflexivity.candidate_reflexive_certificate
