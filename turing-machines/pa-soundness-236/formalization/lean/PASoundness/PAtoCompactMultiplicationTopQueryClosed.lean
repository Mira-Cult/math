import PASoundness.PAtoCompactMultiplicationTopQueryRebased
import PASoundness.PAtoCompactMultiplicationCleanOldTopExclusion

/-! The full-prefix top-row query is obtained from the actual clean-old-graph
endpoint, without a supplied K proof argument. All graph and no-garbage
conditions remain explicit hypotheses. This does not prove graph existence,
product uniqueness, multiplication totality, or PA proof transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationTopQueryClosed
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactMultiplicationTopQueryRebased

/-- A queried new-graph triple at major 30 must be an edge of the suffix
map6, provided old graph10 is clean and the full-prefix row is no-garbage. -/
def top_query : KDerivation
    (imp PASoundness.PAtoCompactProductOldSuffixExclusion.oldClean.encode
      (imp (replace 0 31 (noGarbage 64)).encode
        (imp (replace 6 64 (tripleFormula 30 3 70)).encode
          (both (member 31 3) (graphFormula 6 3 70).encode)))) := by
  have hOld : KDerivation (imp PASoundness.PAtoCompactProductOldSuffixExclusion.oldClean.encode
      (imp PASoundness.PAtoCompactMultiplicationOldTripleIntro.oldTriple.encode (member 30 3))) := by
    simpa [PASoundness.PAtoCompactProductOldSuffixExclusion.oldClean,
      PASoundness.PAtoCompactMultiplicationCleanOldTopExclusion.cleanOld,
      PASoundness.PAtoCompactOldTripleEdgeExtract.oldTriple,
      PASoundness.PAtoCompactMultiplicationOldTripleIntro.oldTriple] using
      PASoundness.PAtoCompactMultiplicationCleanOldTopExclusion.old_major
  exact top_query_full_prefix hOld

theorem top_query_certificate : theoremCode (certificate top_query) =
    imp PASoundness.PAtoCompactProductOldSuffixExclusion.oldClean.encode
      (imp (replace 0 31 (noGarbage 64)).encode
        (imp (replace 6 64 (tripleFormula 30 3 70)).encode
          (both (member 31 3) (graphFormula 6 3 70).encode))) := certificate_correct top_query
end PASoundness.PAtoCompactMultiplicationTopQueryClosed
#print axioms PASoundness.PAtoCompactMultiplicationTopQueryClosed.top_query
#print axioms PASoundness.PAtoCompactMultiplicationTopQueryClosed.top_query_certificate
