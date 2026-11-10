import PASoundness.PAtoCompactProductCleanFilter
import PASoundness.PAtoCompactKuratowskiSyntax

/-! Rebind the selector-created filtered product graph to the fixed fresh
output label 54. This constructs a literal K filter witness; preservation of
product edges, the full product matrix, and multiplication totality are separate. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductCleanFilterFixed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactProductCleanFilter PASoundness.PAtoCompactKuratowskiSyntax
open PASoundness.PAtoCompactSingleton PASoundness.PAtoCompactUnorderedPair
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The exact selector-8 filter has an existential witness bound at label 54.
The displayed input labels are syntactic; their denoted objects may alias. -/
def product_filter_exists_fixed : KDerivation (existsCode 54 (filterCode 54)) := by
  let c := selectorName
  let P := cleanPredicate 55
  let f : Formula := .all 55 (namedFilterBody 6 c 55 P)
  have hc : 55 < c := selector_large
  have hc54 : c ≠ 54 := by omega
  have hc0 : c ≠ 0 := by omega
  have hc1 : c ≠ 1 := by omega
  have hc2 : c ≠ 2 := by omega
  have hc6 : c ≠ 6 := by omega
  have hc20 : c ≠ 20 := by omega
  have hc21 : c ≠ 21 := by omega
  have hc22 : c ≠ 22 := by omega
  have hc50 : c ≠ 50 := by omega
  have hc51 : c ≠ 51 := by omega
  have hc52 : c ≠ 52 := by omega
  have hc53 : c ≠ 53 := by omega
  have hc55 : c ≠ 55 := by omega
  have hcbind : c ∉ f.binders := by
    simp [f,P,namedFilterBody,cleanPredicate,pair_formula_named,namedSingleton,namedPair,
      namedBoth,namedEither,Formula.binders,hc55,hc20,hc21,hc22,hc50,hc51,hc52,hc53]
  have h54names : 54 ∉ f.names := by
    simp [f,P,namedFilterBody,cleanPredicate,pair_formula_named,namedSingleton,namedPair,
      namedBoth,namedEither,Formula.names,Ne.symm hc54]
  have hrename : replace c 54 f = .all 55 (namedFilterBody 6 54 55 P) := by
    simp [f,P,namedFilterBody,cleanPredicate,pair_formula_named,namedSingleton,namedPair,
      namedBoth,namedEither,replace,rename,Ne.symm hc0,Ne.symm hc1,Ne.symm hc2,
      Ne.symm hc6,Ne.symm hc20,Ne.symm hc21,Ne.symm hc22,Ne.symm hc50,
      Ne.symm hc51,Ne.symm hc52,Ne.symm hc53,Ne.symm hc55]
  have ha := (existentialAlpha c 54 f hc54 hcbind h54names).1
  have hsrc : KDerivation (existsCode c f.encode) := by
    simpa [c,f,P,namedFilterBody,namedBoth,Formula.encode,filterCode,filterGraph,
      filterPredicate,CompactProof.both,CompactProof.neg] using product_filter_exists_selector
  rw [hrename] at ha
  have ht : KDerivation (existsCode 54 (Formula.all 55 (namedFilterBody 6 54 55 P)).encode) :=
    .mp hsrc ha
  simpa [P,namedFilterBody,namedBoth,Formula.encode,filterCode,filterGraph,
    filterPredicate,CompactProof.both,CompactProof.neg] using ht

theorem product_filter_exists_fixed_certificate :
    theoremCode (certificate product_filter_exists_fixed) = existsCode 54 (filterCode 54) :=
  certificate_correct product_filter_exists_fixed
end PASoundness.PAtoCompactProductCleanFilterFixed
#print axioms PASoundness.PAtoCompactProductCleanFilterFixed.product_filter_exists_fixed
#print axioms PASoundness.PAtoCompactProductCleanFilterFixed.product_filter_exists_fixed_certificate
