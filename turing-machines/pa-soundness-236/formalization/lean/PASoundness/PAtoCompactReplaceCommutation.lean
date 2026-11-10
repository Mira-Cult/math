import PASoundness.CompactNamed

/-! Syntactic commutation of two uniform replacements. The result is an
identity of syntax, not a semantic or capture-avoidance assertion. -/
namespace PASoundness.PAtoCompactReplaceCommutation

open PASoundness.CompactNamed

/-- Replacements on disjoint source labels commute if neither replacement
targets the other's source. Targets may coincide with each other or with
their own source. -/
theorem rename_commute (p q x y a : Nat) (hpx : p ≠ x) (hqx : q ≠ x) (hyp : y ≠ p) :
    rename p q (rename x y a) = rename x y (rename p q a) := by
  by_cases hp : a = p <;> by_cases hx : a = x <;> simp_all [rename]

/-- Uniform replacement commutes even when its source or target names occur
as binders: binder labels are unchanged by `replace`. Capture-sensitive uses
need their own freshness hypotheses. -/
theorem replace_commute (p q x y : Nat) (f : Formula)
    (hpx : p ≠ x) (hqx : q ≠ x) (hyp : y ≠ p) :
    replace p q (replace x y f) = replace x y (replace p q f) := by
  induction f with
  | truth | bottom => rfl
  | member a b | equal a b => simp [replace, rename_commute p q x y _ hpx hqx hyp]
  | imp a b ia ib => simp [replace, ia, ib]
  | all z a ih | ex z a ih => simp [replace, ih]

end PASoundness.PAtoCompactReplaceCommutation

#print axioms PASoundness.PAtoCompactReplaceCommutation.rename_commute
#print axioms PASoundness.PAtoCompactReplaceCommutation.replace_commute
