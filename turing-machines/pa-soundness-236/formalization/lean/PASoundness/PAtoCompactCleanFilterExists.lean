import PASoundness.PAtoCompactCleanMatrixData
import PASoundness.PAtoCompactRestrictionFilterVacuity
import PASoundness.PAtoCompactKuratowskiSyntax
import PASoundness.CompactQuantifiers

/-! Rename the actual selector-created endpoint filter to the graph binder 6.
This constructs a filter witness for a supplied original graph; it does not
transfer an isomorphism matrix or establish quotient congruence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCleanFilterExists
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSingleton
open PASoundness.PAtoCompactUnorderedPair PASoundness.PAtoCompactKuratowskiSyntax
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactRestrictionFilterVacuity PASoundness.PAtoCompactCleanMatrixData

/-- The selector's computed witness label avoids every concrete binder/name
used by this filter. This uses Cantor-pair lower bounds, not evaluation of the
large encoded predicate. -/
theorem restriction_witness_large : 26 < restrictionName 10 17 0 1 := by
  let P := (edgePredicate 17 0 1).encode
  have h₁ := Cantor.right_le_pair 10 17
  have h₂ := Cantor.left_le_pair (member 10 17) (neg P)
  have h₃ := Cantor.left_le_pair (imp (member 10 17) (neg P)) 1
  change 26 < filterPredicate 10 17 P
  unfold filterPredicate both neg imp member at *
  omega

/-- K constructs an endpoint-filtered graph under the prescribed output
binder 6, keeping original graph 10 and endpoint names 0,1 free. -/
def clean_filter_exists : KDerivation (existsCode 6 filterCode) := by
  let c := restrictionName 10 17 0 1
  let f := namedFilter 10 c 17 0 1
  have hc : 26 < c := restriction_witness_large
  have hc6 : c ≠ 6 := by omega
  have hc0 : c ≠ 0 := by omega
  have hc1 : c ≠ 1 := by omega
  have hc10 : c ≠ 10 := by omega
  have hc17 : c ≠ 17 := by omega
  have hc20 : c ≠ 20 := by omega
  have hc21 : c ≠ 21 := by omega
  have hc22 : c ≠ 22 := by omega
  have hc25 : c ≠ 25 := by omega
  have hc26 : c ≠ 26 := by omega
  have hcbind : c ∉ f.binders := by
    simp [f, namedFilter, edgePredicate, pair_formula_named, namedSingleton, namedPair,
      namedBoth, namedEither, Formula.binders, hc17, hc20, hc21, hc22, hc25, hc26]
  have h6names : 6 ∉ f.names := by
    simp [f, namedFilter, edgePredicate, pair_formula_named, namedSingleton, namedPair,
      namedBoth, namedEither, Formula.names, Ne.symm hc6]
  have hrename : replace c 6 f = namedFilter 10 6 17 0 1 := by
    simp [f, namedFilter, edgePredicate, pair_formula_named, namedSingleton, namedPair,
      namedBoth, namedEither, replace, rename, Ne.symm hc0, Ne.symm hc1, Ne.symm hc10,
      Ne.symm hc17, Ne.symm hc20, Ne.symm hc21, Ne.symm hc22,
      Ne.symm hc25, Ne.symm hc26]
  have ha := (existentialAlpha c 6 f hc6 hcbind h6names).1
  have hsrc : KDerivation (existsCode c f.encode) := by
    simpa only [f, named_filter_code, c, restrictionName] using
      graph_restriction_exists 10 17 0 1 (by decide)
  rw [hrename] at ha
  have ht : KDerivation (existsCode 6 (namedFilter 10 6 17 0 1).encode) := .mp hsrc ha
  simpa only [named_filter_code, filterCode] using ht

theorem clean_filter_exists_certificate : theoremCode (certificate clean_filter_exists) =
    existsCode 6 filterCode := certificate_correct clean_filter_exists

end PASoundness.PAtoCompactCleanFilterExists

#print axioms PASoundness.PAtoCompactCleanFilterExists.restriction_witness_large
#print axioms PASoundness.PAtoCompactCleanFilterExists.clean_filter_exists
#print axioms PASoundness.PAtoCompactCleanFilterExists.clean_filter_exists_certificate
