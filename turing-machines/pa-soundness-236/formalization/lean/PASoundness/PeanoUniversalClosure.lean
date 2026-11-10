import PASoundness.Peano
import PASoundness.SyntaxTransport

/-! Finite universal closure of a named first-order formula. This constructs
syntactic generalizations and proves their semantic elimination; it does not
invoke soundness of the calculus. -/
namespace PASoundness.PeanoUniversalClosure
open FirstOrder FirstOrder.Language

variable {L : Language}

/-- Bind the displayed finite list of free names. -/
def allNames : List Nat → FOL.Formula L → FOL.Formula L
  | [], φ => φ
  | x :: xs, φ => FOL.allAt x (allNames xs φ)

/-- Its free support is exactly the original support minus those names. -/
theorem freeVars_allNames (xs : List Nat) (φ : FOL.Formula L) (x : Nat) :
    x ∈ (allNames xs φ).freeVarFinset ↔ x ∈ φ.freeVarFinset ∧ x ∉ xs := by
  induction xs with
  | nil => simp [allNames]
  | cons y ys ih =>
    simp only [allNames, SyntaxTransport.allAt_freeVars, Finset.mem_erase, ih, List.mem_cons]
    tauto

/-- The explicit list is computed from the given formula. -/
noncomputable def closure (φ : FOL.Formula L) : FOL.Formula L :=
  allNames φ.freeVarFinset.toList φ

/-- All originally free names are bound; no fresh-name assumptions occur. -/
theorem closure_closed (φ : FOL.Formula L) : (closure φ).freeVarFinset = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  have h := (freeVars_allNames φ.freeVarFinset.toList φ x).mp hx
  exact h.2 (Finset.mem_toList.mpr h.1)

/-- The list of binders is introduced by the actual generalization rule. -/
theorem allNames_proves {A : FOL.Formula L → Prop} (xs : List Nat)
    {φ : FOL.Formula L} (h : FOL.Derivation A φ) :
    FOL.Derivation A (allNames xs φ) := by
  induction xs with
  | nil => exact h
  | cons x xs ih => exact .generalize x ih

theorem closure_proves {A : FOL.Formula L → Prop} {φ : FOL.Formula L}
    (h : FOL.Derivation A φ) : FOL.Derivation A (closure φ) :=
  allNames_proves _ h

/-- If the universal closure holds at an assignment, instantiate each
quantifier with that assignment's own value to recover the original formula. -/
theorem allNames_elim {M : Type} [L.Structure M] (xs : List Nat)
    (φ : FOL.Formula L) (v : Nat → M)
    (h : (allNames xs φ).Realize v) : φ.Realize v := by
  induction xs with
  | nil => exact h
  | cons x xs ih =>
    have ht : (allNames xs φ).Realize (Function.update v x (v x)) :=
      (FOL.realize_allAt _ _ _).mp h (v x)
    have hv : Function.update v x (v x) = v := by
      funext y
      by_cases hy : y = x
      · subst y; simp
      · simp [hy]
    rw [hv] at ht
    exact ih ht

theorem closure_elim {M : Type} [L.Structure M] (φ : FOL.Formula L)
    (v : Nat → M) (h : (closure φ).Realize v) : φ.Realize v :=
  allNames_elim _ φ v h

end PASoundness.PeanoUniversalClosure

#print axioms PASoundness.PeanoUniversalClosure.closure_proves
#print axioms PASoundness.PeanoUniversalClosure.closure_elim
