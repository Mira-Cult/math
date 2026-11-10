import PASoundness.CompactNamed

/-! Syntactic cancellation of a fresh intermediate replacement name.
This is not a claim of capture-safe semantics or K equivalence. -/
namespace PASoundness.PAtoCompactReplaceCancellation

open PASoundness.CompactNamed

/-- A fresh intermediate name can be replaced in a second step. -/
theorem rename_cancel (x y z a : Nat) (ha : a ≠ y) :
    rename y z (rename x y a) = rename x z a := by
  simp only [rename]
  split_ifs <;> subst_vars <;> simp_all

/-- Two uniform replacements compose when the intermediate name does not
occur anywhere in the original formula, including its binder labels. -/
theorem replace_cancel (x y z : Nat) (f : Formula) (hy : y ∉ f.names) :
    replace y z (replace x y f) = replace x z f := by
  induction f with
  | truth | bottom => rfl
  | member a b | equal a b =>
      simp only [Formula.names, Finset.mem_insert, Finset.mem_singleton, not_or] at hy
      have ha : a ≠ y := by simpa [Formula.names, eq_comm] using hy.1
      have hb : b ≠ y := by simpa [Formula.names, eq_comm] using hy.2
      simp [replace, rename_cancel x y z a ha, rename_cancel x y z b hb]
  | imp a b ia ib =>
      simp only [Formula.names, Finset.mem_union, not_or] at hy
      simp [replace, ia hy.1, ib hy.2]
  | all w a ia | ex w a ia =>
      simp only [Formula.names, Finset.mem_insert, not_or] at hy
      have hy' : y ∉ a.names := by simpa [Formula.names] using hy.2
      simp [replace, ia hy']

end PASoundness.PAtoCompactReplaceCancellation

#print axioms PASoundness.PAtoCompactReplaceCancellation.rename_cancel
#print axioms PASoundness.PAtoCompactReplaceCancellation.replace_cancel
