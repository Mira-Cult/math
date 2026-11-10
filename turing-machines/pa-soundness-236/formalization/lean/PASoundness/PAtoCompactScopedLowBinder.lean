import PASoundness.PAtoCompactVacuousUniversal

/-! Every generated binder lies above each active name. This syntactic bound
is useful when instantiating an active name at a lower, possibly already free,
name without capturing that name. -/
namespace PASoundness.PAtoCompactScopedLowBinder

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactScopedEqualityReplace PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactTermGraphBinderRange

/-- Names no greater than an active name cannot occur as generated binders.
The active name need not be distinct from any other active name or free name. -/
theorem below_active_not_binder {n : Nat} (φ : Peano.language.BoundedFormula Nat n) :
    ∀ (bound : Fin n → Nat) (i : Fin n) (a : Nat), a ≤ bound i →
      a ∉ (scopedFormula n φ bound).binders := by
  induction φ with
  | falsum =>
      intro bound i a ha
      simp [scopedFormula, Formula.binders]
  | @equal n t u =>
      intro bound i a ha h
      rw [scoped_equal_frame] at h
      have hge := equalityFrame_binders_ge (Sum.elim id bound) t u
        (scopeBase (.equal t u) bound) a h
      have hlt := bound_lt_scopeBase (.equal t u) bound i
      omega
  | rel r ts => exact nomatch r
  | imp a b iha ihb =>
      intro bound i z hz h
      simp only [scopedFormula, Formula.binders, Finset.mem_union] at h
      cases h with
      | inl h => exact iha bound i z hz h
      | inr h => exact ihb bound i z hz h
  | @all n body ih =>
      intro bound i a ha h
      let x := scopeBase (.all body) bound
      have hlt : bound i < x := bound_lt_scopeBase (.all body) bound i
      change a ∈ (Formula.all x (.imp (domainAt (x+1) x)
        (scopedFormula (n+1) body (Fin.snoc bound x)))).binders at h
      simp only [Formula.binders, Finset.mem_insert, Finset.mem_union] at h
      rcases h with he | hd | hs
      · omega
      · have hp := domainAt_private (x+1) x a hd
        omega
      · have hn := ih (Fin.snoc bound x) (Fin.castSucc i) a (by simpa using ha)
        exact hn hs

end PASoundness.PAtoCompactScopedLowBinder

#print axioms PASoundness.PAtoCompactScopedLowBinder.below_active_not_binder
