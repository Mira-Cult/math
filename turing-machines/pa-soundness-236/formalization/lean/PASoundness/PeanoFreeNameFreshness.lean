import PASoundness.PeanoFreeNamePermutation

/-! Free-variable support under capture-safe renaming of PA formulas.
These are syntax lemmas; they do not assert a PA comprehension instance. -/
namespace PASoundness.PeanoFreeNameFreshness
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic

/-- A renamed formula has exactly the image of its original free-variable
support, for any name map, including noninjective maps. -/
theorem free_vars_image (φ : Peano.Formula) (f : Nat → Nat) (z : Nat) :
    z ∈ (φ.subst (fun n => .var (f n))).freeVarFinset ↔
      ∃ y ∈ φ.freeVarFinset, f y = z := by
  rw [SyntaxTransport.formula_subst_freeVars]
  simp only [FirstOrder.Language.Term.varFinset, Finset.mem_singleton]
  simp only [eq_comm]

/-- If no free name is mapped to `z`, then `z` is fresh after renaming. -/
theorem fresh_of_avoids (φ : Peano.Formula) (f : Nat → Nat) (z : Nat)
    (h : ∀ y ∈ φ.freeVarFinset, f y ≠ z) :
    z ∉ (φ.subst (fun n => .var (f n))).freeVarFinset := by
  rw [free_vars_image]
  rintro ⟨y, hy, he⟩
  exact h y hy he

/-- The same freshness criterion for the explicit finite swap-list action. -/
theorem permuted_fresh (xs : List (Nat × Nat)) (φ : Peano.Formula) (z : Nat)
    (h : ∀ y ∈ φ.freeVarFinset, PeanoFreeNamePermutation.applyName xs y ≠ z) :
    z ∉ (PeanoFreeNamePermutation.applyFormula xs φ).freeVarFinset := by
  rw [PeanoFreeNamePermutation.applyFormula_eq]
  exact fresh_of_avoids φ (PeanoFreeNamePermutation.applyName xs) z h

end PASoundness.PeanoFreeNameFreshness

#print axioms PASoundness.PeanoFreeNameFreshness.free_vars_image
#print axioms PASoundness.PeanoFreeNameFreshness.permuted_fresh
