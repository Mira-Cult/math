import PASoundness.PAtoCompactScopedActiveReplace
import PASoundness.SyntaxTransport

/-! Source-support bounds for capture-avoiding substitution into bounded PA
formulas.  Bound levels and free names remain distinct, even if their chosen
interpreted labels coincide. -/
namespace PASoundness.PAtoCompactSuccSubstSyntax

open FirstOrder FirstOrder.Language
open PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.SyntaxTransport

/-- Single-variable source substitution, with bound levels left to
`BoundedFormula.subst`'s capture-avoiding lifting. -/
def singleSubst (x : Nat) (t : Peano.Term) (a : Nat) : Peano.Term :=
  if a = x then t else .var a

/-- Exact free-name support after source substitution, at every binder depth.
The replacement term contributes names only when x is actually free. -/
theorem singleSubst_free_support {n : Nat}
    (φ : Peano.language.BoundedFormula Nat n) (x : Nat) (t : Peano.Term) :
    (φ.subst (singleSubst x t)).freeVarFinset =
      φ.freeVarFinset.erase x ∪ t.varFinset.filter (fun _ => x ∈ φ.freeVarFinset) := by
  classical
  ext z
  rw [formula_subst_freeVars]
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_filter]
  constructor
  · rintro ⟨a, ha, hz⟩
    by_cases hax : a = x
    · subst a
      right
      exact ⟨by simpa [singleSubst] using hz, ha⟩
    · left
      have hza : z = a := by simpa [singleSubst, hax, Term.varFinset] using hz
      subst z
      exact ⟨hax, ha⟩
  · rintro (⟨hzx, hz⟩ | ⟨hz, hx⟩)
    · exact ⟨z, hz, by simp [singleSubst, hzx, Term.varFinset]⟩
    · exact ⟨x, hx, by simpa [singleSubst] using hz⟩

/-- Relabeling a term maps its finite variable support, including when the
relabeling is not injective. -/
theorem relabel_varFinset {α β : Type} [DecidableEq α] [DecidableEq β]
    (t : Peano.language.Term α) (f : α → β) :
    (t.relabel f).varFinset = t.varFinset.image f := by
  induction t with
  | var a => simp [Term.relabel, Term.varFinset]
  | func F ts ih =>
      simp only [Term.relabel, Term.varFinset, ih]
      ext a
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨i, b, hb, rfl⟩
        exact ⟨b, ⟨i, hb⟩, rfl⟩
      · rintro ⟨b, ⟨i, hb⟩, rfl⟩
        exact ⟨i, b, hb, rfl⟩

/-- Every interpreted variable in the left substituted equality term lies
below the allocation base computed from that same substituted equality.
This includes labels assigned to bound levels, with no injectivity or
freshness condition on the bound environment. -/
theorem left_substituted_names_lt {n : Nat}
    (s t : Peano.language.Term (Nat ⊕ Fin n)) (σ : Nat → Peano.Term)
    (bound : Fin n → Nat) (a : Nat)
    (ha : a ∈ ((s.subst (liftSub n σ)).relabel (Sum.elim id bound)).varFinset) :
    a < scopeBase ((.equal s t : Peano.language.BoundedFormula Nat n).subst σ) bound := by
  rw [relabel_varFinset] at ha
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
  exact eq_left_name_lt (s.subst (liftSub n σ)) (t.subst (liftSub n σ)) bound v hv

/-- The corresponding bound for the right equality term. -/
theorem right_substituted_names_lt {n : Nat}
    (s t : Peano.language.Term (Nat ⊕ Fin n)) (σ : Nat → Peano.Term)
    (bound : Fin n → Nat) (a : Nat)
    (ha : a ∈ ((t.subst (liftSub n σ)).relabel (Sum.elim id bound)).varFinset) :
    a < scopeBase ((.equal s t : Peano.language.BoundedFormula Nat n).subst σ) bound := by
  rw [relabel_varFinset] at ha
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
  exact eq_right_name_lt (s.subst (liftSub n σ)) (t.subst (liftSub n σ)) bound v hv

/-- A common allocation base bounds both substitutions, even when their
free-variable supports differ. -/
def comparisonBase {n : Nat} (φ : Peano.language.BoundedFormula Nat n)
    (σ τ : Nat → Peano.Term) (bound : Fin n → Nat) : Nat :=
  max (scopeBase (φ.subst σ) bound) (scopeBase (φ.subst τ) bound)

theorem left_substituted_names_lt_comparison {n : Nat}
    (s t : Peano.language.Term (Nat ⊕ Fin n)) (σ τ : Nat → Peano.Term)
    (bound : Fin n → Nat) (a : Nat)
    (ha : a ∈ ((s.subst (liftSub n σ)).relabel (Sum.elim id bound)).varFinset) :
    a < comparisonBase (.equal s t) σ τ bound := by
  have h := left_substituted_names_lt s t σ bound a ha
  exact Nat.lt_of_lt_of_le h (Nat.le_max_left _ _)

theorem right_substituted_names_lt_comparison {n : Nat}
    (s t : Peano.language.Term (Nat ⊕ Fin n)) (σ τ : Nat → Peano.Term)
    (bound : Fin n → Nat) (a : Nat)
    (ha : a ∈ ((t.subst (liftSub n σ)).relabel (Sum.elim id bound)).varFinset) :
    a < comparisonBase (.equal s t) σ τ bound := by
  have h := right_substituted_names_lt s t σ bound a ha
  exact Nat.lt_of_lt_of_le h (Nat.le_max_left _ _)

/-- All four substituted term supports are below the common base, including
the target substitution when its own scope base is the larger one. -/
theorem comparison_term_supports {n : Nat}
    (s t : Peano.language.Term (Nat ⊕ Fin n)) (σ τ : Nat → Peano.Term)
    (bound : Fin n → Nat) :
    (∀ a ∈ ((s.subst (liftSub n σ)).relabel (Sum.elim id bound)).varFinset,
      a < comparisonBase (.equal s t) σ τ bound) ∧
    (∀ a ∈ ((t.subst (liftSub n σ)).relabel (Sum.elim id bound)).varFinset,
      a < comparisonBase (.equal s t) σ τ bound) ∧
    (∀ a ∈ ((s.subst (liftSub n τ)).relabel (Sum.elim id bound)).varFinset,
      a < comparisonBase (.equal s t) σ τ bound) ∧
    (∀ a ∈ ((t.subst (liftSub n τ)).relabel (Sum.elim id bound)).varFinset,
      a < comparisonBase (.equal s t) σ τ bound) := by
  refine ⟨left_substituted_names_lt_comparison s t σ τ bound,
    right_substituted_names_lt_comparison s t σ τ bound, ?_, ?_⟩
  · intro a ha
    exact Nat.lt_of_lt_of_le (left_substituted_names_lt s t τ bound a ha) (Nat.le_max_right _ _)
  · intro a ha
    exact Nat.lt_of_lt_of_le (right_substituted_names_lt s t τ bound a ha) (Nat.le_max_right _ _)

end PASoundness.PAtoCompactSuccSubstSyntax

#print axioms PASoundness.PAtoCompactSuccSubstSyntax.left_substituted_names_lt
#print axioms PASoundness.PAtoCompactSuccSubstSyntax.singleSubst_free_support
#print axioms PASoundness.PAtoCompactSuccSubstSyntax.right_substituted_names_lt
#print axioms PASoundness.PAtoCompactSuccSubstSyntax.left_substituted_names_lt_comparison
#print axioms PASoundness.PAtoCompactSuccSubstSyntax.right_substituted_names_lt_comparison
#print axioms PASoundness.PAtoCompactSuccSubstSyntax.comparison_term_supports
