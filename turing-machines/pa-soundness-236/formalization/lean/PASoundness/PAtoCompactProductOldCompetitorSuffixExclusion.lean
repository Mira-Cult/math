import PASoundness.PAtoCompactProductOldSuffixExclusion

/-! Capture-safe specialization of old/suffix edge exclusion to competitor
coordinates 7 and 8. The same outer member and inner/outer pair descriptions
are retained; no uniqueness of pair representatives or graph construction is
assumed. The clean graph and literal suffix filter remain explicit K premises. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOldCompetitorSuffixExclusion
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactProductOldSuffixExclusion
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Competitor coordinate query sharing the actual outer object 63. -/
def competitorQuery : Formula := replace 4 8 (replace 3 7 query63)
private def F : Formula := .all 35 (namedFilterBody 45 40 35 (Formula.member 32 35).not)
private def source : Formula := .imp oldClean (.imp query63 (.imp F
  (.imp (.member 40 5) (Formula.member 10 63).not)))
private def at7 : Formula := replace 3 7 source
private def at8 : Formula := replace 4 8 at7

/-- For a suffix output, the same competitor edge cannot belong to the
clean old graph. -/
def old_competitor_excluded : KDerivation (imp oldClean.encode (imp competitorQuery.encode
    (imp (filterGraph 45 40 35 (neg (member 32 35)))
      (imp (member 40 5) (neg (member 10 63)))))) := by
  have h0 : KDerivation source.encode := by
    simpa [source,F,namedFilterBody,namedBoth,Formula.not,Formula.encode,filterGraph,
      filterPredicate,both,neg] using old_edge_excluded
  have h1 : KDerivation at7.encode := .mp (.generalize 3 h0)
    (universalInstance 3 7 source (by decide) (by decide) (by decide))
  have h2 : KDerivation at8.encode := .mp (.generalize 4 h1)
    (universalInstance 4 8 at7 (by decide) (by decide) (by decide))
  have hshape : at8 = .imp oldClean (.imp competitorQuery (.imp F
      (.imp (.member 40 5) (Formula.member 10 63).not))) := by decide
  rw [hshape] at h2
  simpa [F,namedFilterBody,namedBoth,Formula.not,Formula.encode,filterGraph,
    filterPredicate,both,neg] using h2

theorem old_competitor_excluded_certificate : theoremCode (certificate old_competitor_excluded) =
    imp oldClean.encode (imp competitorQuery.encode
      (imp (filterGraph 45 40 35 (neg (member 32 35)))
        (imp (member 40 5) (neg (member 10 63))))) :=
  certificate_correct old_competitor_excluded
end PASoundness.PAtoCompactProductOldCompetitorSuffixExclusion
#print axioms PASoundness.PAtoCompactProductOldCompetitorSuffixExclusion.old_competitor_excluded
#print axioms PASoundness.PAtoCompactProductOldCompetitorSuffixExclusion.old_competitor_excluded_certificate
