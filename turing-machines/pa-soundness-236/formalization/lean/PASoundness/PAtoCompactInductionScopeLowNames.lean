import PASoundness.PAtoCompactScopedLowBinder
import PASoundness.PAtoCompactFreeNames
import PASoundness.PAtoCompactDirectGeneralization

/-! Lower names absent from the opened source are absent from every name in
its scoped K translation. This is a syntactic allocation lemma, not a K proof
or an induction theorem. -/
namespace PASoundness.PAtoCompactInductionScopeLowNames
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactDirectGeneralization
open PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactScopedLowBinder PASoundness.PAtoCompactFreeNames

/-- For an opened PA formula with active label t, any smaller source-fresh
name occurs neither freely nor as a binder in the translated named formula. -/
theorem scope_low_name_fresh (φ : Peano.Formula) (x t n : Nat)
    (hlt : n < t) (hf : n ∉ (allAtBody x φ).freeVarFinset) :
    n ∉ (scopeAt φ x t).names := by
  let B := allAtBody x φ
  let v : Fin 1 → Nat := Fin.snoc Fin.elim0 t
  have hbind : n ∉ (scopedFormula 1 B v).binders := by
    apply below_active_not_binder B v (Fin.last 0) n
    simpa [v] using Nat.le_of_lt hlt
  have hfree : n ∉ (scopedFormula 1 B v).free := by
    intro h
    have hh := scopedFormula_free_subset B v h
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hh
    rcases hh with h | ⟨i, hi⟩
    · exact hf h
    · have hit : v i = t := by
        have : i = Fin.last 0 := Subsingleton.elim _ _
        subst i
        simp [v]
      rw [hit] at hi
      omega
  change n ∉ (scopedFormula 1 B v).names
  rw [Formula.names_eq_free_union_binders]
  simp [hfree,hbind]

/-- The active label is never introduced as an internal binder. -/
theorem scope_active_not_binder (φ : Peano.Formula) (x t : Nat) :
    t ∉ (scopeAt φ x t).binders := by
  apply below_active_not_binder (allAtBody x φ) (Fin.snoc Fin.elim0 t) (Fin.last 0) t
  simp

end PASoundness.PAtoCompactInductionScopeLowNames

#print axioms PASoundness.PAtoCompactInductionScopeLowNames.scope_low_name_fresh
#print axioms PASoundness.PAtoCompactInductionScopeLowNames.scope_active_not_binder
