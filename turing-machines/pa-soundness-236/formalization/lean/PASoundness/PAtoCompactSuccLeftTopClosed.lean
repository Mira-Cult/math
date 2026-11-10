import PASoundness.PAtoCompactSuccLeftTopCase
import PASoundness.PAtoCompactSuccTopWitness
import PASoundness.PAtoCompactSuccTopUnique
import PASoundness.PAtoCompactSuccCleanEndpoint

/-! Compose the exact supplied-graph top-source case with its actual K
endpoint, witness and encoded-irreflexivity derivations. The uniform edge
split and all displayed graph hypotheses remain object-level antecedents;
no graph collection, quotient congruence or PA interpretation is asserted. -/
namespace PASoundness.PAtoCompactSuccLeftTopClosed
open PASoundness.CompactProof
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactSuccLeftTopCase
open PASoundness.PAtoCompactSuccTopWitness PASoundness.PAtoCompactSuccTopUnique
open PASoundness.PAtoCompactSuccCleanEndpoint

/-- K derives the left bijection's top-source witness from the explicitly
supplied graph, successor, clean-edge, irreflexivity and split formulas. -/
def top_case_closed : KDerivation (imp cleanGraph (imp sourceIrreflexive (imp uniformSplit
    (imp targetSuccessor (imp newGraph (imp newPair
      (imp (equal 2 0) (existsCode 3 witnessBody.encode)))))))) :=
  top_case target_top_member new_top_edge (top_unique_of_endpoint clean_edge_04)

theorem top_case_closed_certificate : theoremCode (certificate top_case_closed) =
    imp cleanGraph (imp sourceIrreflexive (imp uniformSplit
      (imp targetSuccessor (imp newGraph (imp newPair
        (imp (equal 2 0) (existsCode 3 witnessBody.encode))))))) :=
  certificate_correct top_case_closed

end PASoundness.PAtoCompactSuccLeftTopClosed

#print axioms PASoundness.PAtoCompactSuccLeftTopClosed.top_case_closed
#print axioms PASoundness.PAtoCompactSuccLeftTopClosed.top_case_closed_certificate
