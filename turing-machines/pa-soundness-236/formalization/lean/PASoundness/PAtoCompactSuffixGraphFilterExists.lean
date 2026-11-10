import PASoundness.PAtoCompactRestrictionWitnessEight
import PASoundness.PAtoCompactScopedActiveReplace
import PASoundness.PAtoCompactSuffixGraphForwardCoverage

/-! Construct the exact endpoint filter of original graph6 onto suffixes40/41
at the fresh graph binder8. This is finite K proof data for filter existence,
not a suffix isomorphism or an addition output-transport theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuffixGraphFilterExists
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactRestrictionFilterVacuity PASoundness.PAtoCompactRestrictionWitnessEight
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactSuffixGraphForwardCoverage
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def old : Formula := .ex 8 (namedFilter 6 8 14 2 5)
private def first : Formula := replace 2 40 old
private theorem target_shape : replace 5 41 first = .ex 8 (namedFilter 6 8 14 40 41) := by decide

/-- K constructs some graph8 satisfying the exact retained-edge filter for
sets40 and41. Syntactic labels are fixed; their object values may coincide. -/
noncomputable def suffix_graph_filter_exists : KDerivation (existsCode 8 graphFilter) := by
  have hbase : KDerivation old.encode := by
    simpa only [old,Formula.encode,named_filter_code] using restriction_exists_eight
  have h40 := replace_derivation 2 40 old (by decide) (by decide) hbase
  have h41 := replace_derivation 5 41 first (by decide) (by decide)
    (by simpa only [first] using h40)
  rw [target_shape] at h41
  simpa only [Formula.encode,named_filter_code,graphFilter] using h41

theorem suffix_graph_filter_exists_certificate :
    theoremCode (certificate suffix_graph_filter_exists) = existsCode 8 graphFilter :=
  certificate_correct suffix_graph_filter_exists

end PASoundness.PAtoCompactSuffixGraphFilterExists

#print axioms PASoundness.PAtoCompactSuffixGraphFilterExists.suffix_graph_filter_exists
#print axioms PASoundness.PAtoCompactSuffixGraphFilterExists.suffix_graph_filter_exists_certificate
