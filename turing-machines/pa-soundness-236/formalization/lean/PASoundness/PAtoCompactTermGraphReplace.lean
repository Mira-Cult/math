import PASoundness.PAtoCompactTermGraphBinderRange
import PASoundness.PAtoCompactTermGraphBlockShift

/-! Syntactic commutation of named replacement with generated term graphs.
This does not assert K equivalence of formulas with differing free names. -/
namespace PASoundness.PAtoCompactTermGraphReplace

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactTermGraphBlockShift

/-- Replacing a name below the graph's private block commutes literally with
term-graph construction, including its output label. The target name may
occur inside the private block: the equation alone does not claim avoidance
of target capture. -/
theorem replace_termGraph {α : Type} (varName : α → Nat)
    (t : Peano.language.Term α) (out base x y : Nat) (hx : x < base) :
    replace x y (termGraph varName t out base) =
      termGraph (rename x y ∘ varName) t (rename x y out) base := by
  rw [← termGraph_map_eq_replace_below varName t out base x y hx]
  apply termGraph_shift
  intro i hi
  simp [rename, show base + i ≠ x by omega]

/-- If the target also lies below the block it is not bound by the graph;
this gives the target-freshness fact needed by capture-safe uses. -/
theorem replace_target_unbound {α : Type} (varName : α → Nat)
    (t : Peano.language.Term α) (out base y : Nat) (hy : y < base) :
    y ∉ (termGraph varName t out base).binders :=
  termGraph_below_not_binder varName t out base y hy

end PASoundness.PAtoCompactTermGraphReplace

#print axioms PASoundness.PAtoCompactTermGraphReplace.replace_termGraph
#print axioms PASoundness.PAtoCompactTermGraphReplace.replace_target_unbound
