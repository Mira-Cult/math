import PASoundness.PAtoCompactRestrictionFilterVacuity
import PASoundness.PAtoCompactKuratowskiSyntax
import PASoundness.CompactQuantifiers

/-! A fresh name for the exact selector-created restricted graph. This is
K proof data for a filter, not an isomorphism, quotient or PA interpretation.
Code 1 is literally `member 0 0`. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictionWitnessEight
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSingleton
open PASoundness.PAtoCompactUnorderedPair PASoundness.PAtoCompactKuratowskiSyntax
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactRestrictionFilterVacuity
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The exact computed selector name exceeds all visible and internal
restriction labels, using Cantor bounds instead of evaluating the code. -/
theorem restriction_witness_large : 26 < restrictionName 6 14 2 5 := by
  let P := (edgePredicate 14 2 5).encode
  have h₁ := Cantor.right_le_pair 6 14
  have h₂ := Cantor.left_le_pair (member 6 14) (neg P)
  have h₃ := Cantor.left_le_pair (imp (member 6 14) (neg P)) 1
  change 26 < filterPredicate 6 14 P
  unfold filterPredicate both neg imp member at *
  omega

/-- For the fixed source graph 6, selector test 14 and endpoint sets 2,5,
K derives existence of the exact restricted graph with output name 8. The
object denotations may coincide; the fixed syntactic labels are distinct
from all internal binders. No property beyond filter existence is asserted. -/
def restriction_exists_eight : KDerivation
    (existsCode 8 (filterGraph 6 8 14 (edgePredicate 14 2 5).encode)) := by
  let c := restrictionName 6 14 2 5
  let f := namedFilter 6 c 14 2 5
  have hc : 26 < c := restriction_witness_large
  have hc8 : c ≠ 8 := by omega
  have hc2 : c ≠ 2 := by omega
  have hc5 : c ≠ 5 := by omega
  have hc6 : c ≠ 6 := by omega
  have hc14 : c ≠ 14 := by omega
  have hc20 : c ≠ 20 := by omega
  have hc21 : c ≠ 21 := by omega
  have hc22 : c ≠ 22 := by omega
  have hc25 : c ≠ 25 := by omega
  have hc26 : c ≠ 26 := by omega
  have hcbind : c ∉ f.binders := by
    simp [f, namedFilter, edgePredicate, pair_formula_named, namedSingleton, namedPair,
      namedBoth, namedEither, Formula.binders, hc14, hc20, hc21, hc22, hc25, hc26]
  have h8names : 8 ∉ f.names := by
    simp [f, namedFilter, edgePredicate, pair_formula_named, namedSingleton, namedPair,
      namedBoth, namedEither, Formula.names, Ne.symm hc8]
  have hrename : replace c 8 f = namedFilter 6 8 14 2 5 := by
    simp [f, namedFilter, edgePredicate, pair_formula_named, namedSingleton, namedPair,
      namedBoth, namedEither, replace, rename, Ne.symm hc2, Ne.symm hc5, Ne.symm hc6,
      Ne.symm hc14, Ne.symm hc20, Ne.symm hc21, Ne.symm hc22,
      Ne.symm hc25, Ne.symm hc26]
  have ha := (existentialAlpha c 8 f hc8 hcbind h8names).1
  have hsrc : KDerivation (existsCode c f.encode) := by
    simpa only [f, named_filter_code, c, restrictionName] using
      graph_restriction_exists 6 14 2 5 (by decide)
  rw [hrename] at ha
  have ht : KDerivation (existsCode 8 (namedFilter 6 8 14 2 5).encode) := .mp hsrc ha
  simpa only [named_filter_code] using ht

theorem restriction_exists_eight_certificate :
    theoremCode (certificate restriction_exists_eight) =
      existsCode 8 (filterGraph 6 8 14 (edgePredicate 14 2 5).encode) :=
  certificate_correct restriction_exists_eight

end PASoundness.PAtoCompactRestrictionWitnessEight

#print axioms PASoundness.PAtoCompactRestrictionWitnessEight.restriction_exists_eight
#print axioms PASoundness.PAtoCompactRestrictionWitnessEight.restriction_exists_eight_certificate
