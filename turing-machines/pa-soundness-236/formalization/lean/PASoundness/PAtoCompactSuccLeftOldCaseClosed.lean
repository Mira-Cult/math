import PASoundness.PAtoCompactSuccLeftOldCase
import PASoundness.PAtoCompactSuccCongruenceEdgeSplit
import PASoundness.PAtoCompactSuccLeftUniformGuard
import PASoundness.PAtoCompactSuccCleanEndpoint

/-! Close the old-source witness-transfer proof-data premises using the
actual supplied-graph edge split and clean-edge endpoint derivations. The
object-level old matrix, cleanliness, irreflexivity, successor, new pair,
new graph, and old-source membership are still explicit antecedents. -/
namespace PASoundness.PAtoCompactSuccLeftOldCaseClosed
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactSuccLeftOldCase
open PASoundness.PAtoCompactSuccCongruenceEdgeSplit PASoundness.PAtoCompactSuccLeftUniformGuard
open PASoundness.PAtoCompactSuccCleanEndpoint

/-- K transfers an old source's existing bijection witness to the supplied
successor target and extended graph under the listed object-level hypotheses. -/
def old_source_case_closed : KDerivation
    (imp oldMatrix (imp cleanGraph (imp sourceIrreflexive
      (imp targetSuccessor (imp newGraph (imp newPair (imp (member 0 2)
        (existsCode 3 newBody.encode)))))))) :=
  old_source_case edge_split_target4 (uniform_guard clean_edge_target_24)

theorem old_source_case_closed_certificate : theoremCode (certificate old_source_case_closed) =
    imp oldMatrix (imp cleanGraph (imp sourceIrreflexive
      (imp targetSuccessor (imp newGraph (imp newPair (imp (member 0 2)
        (existsCode 3 newBody.encode))))))) := certificate_correct old_source_case_closed

end PASoundness.PAtoCompactSuccLeftOldCaseClosed

#print axioms PASoundness.PAtoCompactSuccLeftOldCaseClosed.old_source_case_closed
#print axioms PASoundness.PAtoCompactSuccLeftOldCaseClosed.old_source_case_closed_certificate
