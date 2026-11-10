import PASoundness.PAtoCompactRestrictionFilterVacuity
import PASoundness.PAtoCompactKuratowskiSyntax

/-! A concrete sufficient name-freshness condition for the graph filter. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictionFresh19
open PASoundness.CompactNamed PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactRestrictionFilterVacuity
open PASoundness.PAtoCompactKuratowskiSyntax PASoundness.PAtoCompactSingleton
open PASoundness.PAtoCompactUnorderedPair

/-- Pairwise fresh displayed labels ensure that the graph witness name 19
does not occur, freely or bound, in the exact endpoint-filter formula. -/
theorem filter_fresh_19 (g h t x y : Nat)
    (fresh : [g,h,t,x,y,19,20,21,22,25,26].Nodup) :
    19 ∉ (namedFilter g h t x y).names := by
  have hg : g ≠ 19 := by intro he; subst g; simp at fresh
  have hh : h ≠ 19 := by intro he; subst h; simp at fresh
  have ht : t ≠ 19 := by intro he; subst t; simp at fresh
  have hx : x ≠ 19 := by intro he; subst x; simp at fresh
  have hy : y ≠ 19 := by intro he; subst y; simp at fresh
  have hp : 19 ∉ (pairFormula t 25 26).names := by
    rw [pair_formula_named]
    simp [namedSingleton, namedPair, namedBoth, namedEither, Formula.names, Ne.symm ht]
  simp [namedFilter, edgePredicate, namedBoth, Formula.names, hp,
    Ne.symm hg, Ne.symm hh, Ne.symm ht, Ne.symm hx, Ne.symm hy]

end PASoundness.PAtoCompactRestrictionFresh19

#print axioms PASoundness.PAtoCompactRestrictionFresh19.filter_fresh_19
