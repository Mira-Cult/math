import PASoundness.PAtoCompactTermGraphBinderRange
import PASoundness.PAtoCompactGuardElimination

/-! Capture-sensitive syntactic replacement for the successor template. This
is a literal identity, not a K equivalence of formulas with different free
operand labels. -/
namespace PASoundness.PAtoCompactSuccTermReplacement

open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactAlphaMapOne PASoundness.PAtoCompactGuardElimination
open PASoundness.PAtoCompactTermGraphBinderRange

/-- A label below the successor template's private block is not a binder,
independently of whether the two input labels coincide. -/
theorem succAt_below_not_binder (base a out x : Nat) (hx : x < base + 2) :
    x ∉ (succAt base a out).binders := by
  intro h
  have hl := succAt_private base a out x h
  omega

/-- Replacing a name below the private block commutes with the successor
template, changing both input labels. This identity does not claim that the
new name avoids capture unless that is separately checked. -/
theorem replace_succAt (base a out x y : Nat) (hx : x < base + 2) :
    replace x y (succAt base a out) =
      succAt base (rename x y a) (rename x y out) := by
  rw [← map_eq_replace x y (succAt base a out) (succAt_below_not_binder base a out x hx)]
  unfold succAt
  rw [mapNames_compose]
  congr 1
  funext z
  by_cases h0 : z = 0
  · simp [twoMap, h0]
  · by_cases h1 : z = 1
    · simp [twoMap, h1]
    · have hne : base + 2 + z ≠ x := by omega
      simp [twoMap, h0, h1, rename, hne]

/-- A replacement target below the private block is not bound. Existential
alpha conversion additionally requires target absence from all body names. -/
theorem replace_target_unbound (base a out y : Nat) (hy : y < base + 2) :
    y ∉ (succAt base a out).binders := succAt_below_not_binder base a out y hy

end PASoundness.PAtoCompactSuccTermReplacement

#print axioms PASoundness.PAtoCompactSuccTermReplacement.succAt_below_not_binder
#print axioms PASoundness.PAtoCompactSuccTermReplacement.replace_succAt
#print axioms PASoundness.PAtoCompactSuccTermReplacement.replace_target_unbound
