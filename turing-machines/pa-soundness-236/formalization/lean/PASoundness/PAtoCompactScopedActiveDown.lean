import PASoundness.PAtoCompactScopedActiveReplace

/-! Downward replacement of an active name in an equality atom. The target
may already occur freely in the source, or alias another active name. -/
namespace PASoundness.PAtoCompactScopedActiveDown

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactScopedEqualityReplace PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactVacuousQuantifierFree PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactEqualityGraphTruth

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Replacement by a lower name may merge the active name with names already
free in the source. The source occurrence condition prevents replacing an
unrelated free occurrence of the old active name. -/
noncomputable def scoped_equal_active_down {n : Nat}
    (t u : Peano.language.Term (Nat ⊕ Fin n)) (bound : Fin n → Nat) (i : Fin n) (y : Nat)
    (hfree : bound i ∉ (.equal t u : Peano.language.BoundedFormula Nat n).freeVarFinset)
    (hdown : y < bound i) :
    KBoth (replace (bound i) y (scopedFormula n (.equal t u) bound))
      (scopedFormula n (.equal t u) (rename (bound i) y ∘ bound)) := by
  let a := bound i
  let v := Sum.elim id bound
  let bound' := rename a y ∘ bound
  let v' := Sum.elim id bound'
  let b := scopeBase (.equal t u) bound
  let c := scopeBase (.equal t u) bound'
  let d := max b c + 1
  have hab : a < b := bound_lt_scopeBase (.equal t u) bound i
  have had : a < d := by dsimp [d]; omega
  have hyd : y < d := by omega
  have hyb : y ∉ (equalityFrame v t u b).binders :=
    target_not_bound v t u b y (by omega)
  have ht : ∀ z ∈ t.varFinset, rename a y (v z) = v' z := by
    intro z hz
    cases z with
    | inl x =>
        have hxf : x ∈ (.equal t u : Peano.language.BoundedFormula Nat n).freeVarFinset := by
          change x ∈ t.varFinsetLeft ∪ u.varFinsetLeft
          exact Finset.mem_union_left _ (inl_mem_left t x hz)
        have hxa : x ≠ a := by intro h; subst x; exact hfree hxf
        simp [v, v', rename, hxa]
    | inr j => rfl
  have hu : ∀ z ∈ u.varFinset, rename a y (v z) = v' z := by
    intro z hz
    cases z with
    | inl x =>
        have hxf : x ∈ (.equal t u : Peano.language.BoundedFormula Nat n).freeVarFinset := by
          change x ∈ t.varFinsetLeft ∪ u.varFinsetLeft
          exact Finset.mem_union_right _ (inl_mem_left u x hz)
        have hxa : x ≠ a := by intro h; subst x; exact hfree hxf
        simp [v, v', rename, hxa]
    | inr j => rfl
  have htold := eq_left_name_lt t u bound
  have huold := eq_right_name_lt t u bound
  have htnew := eq_left_name_lt t u bound'
  have hunew := eq_right_name_lt t u bound'
  have high := equalityFrame_replace_base_transport v t u b d a y hab had hyd hyb
    htold huold
    (by intro z hz; have h := htold z hz; change v z < b at h; dsimp [d]; omega)
    (by intro z hz; have h := huold z hz; change v z < b at h; dsimp [d]; omega)
  have newbase := equalityFrame_base_transport v' t u d c
    (by intro z hz; have h := htnew z hz; change v' z < c at h; dsimp [d]; omega)
    (by intro z hz; have h := hunew z hz; change v' z < c at h; dsimp [d]; omega)
    htnew hunew
  rw [scoped_equal_frame, scoped_equal_frame]
  rw [replace_equalityFrame v t u b a y hab]
  rw [equalityFrame_name_agree t u (rename a y ∘ v) v' d ht hu] at high
  exact ⟨compose high.1 newbase.1, compose newbase.2 high.2⟩

/-- Downward active replacement for quantifier-free bounded PA formulas.
The lower target may occur freely in the source. -/
noncomputable def scoped_qfree_active_down {n : Nat}
    {φ : Peano.language.BoundedFormula Nat n} (h : ScopedQFree φ)
    (bound : Fin n → Nat) (i : Fin n) (y : Nat)
    (hfree : bound i ∉ φ.freeVarFinset) (hdown : y < bound i) :
    KBoth (replace (bound i) y (scopedFormula n φ bound))
      (scopedFormula n φ (rename (bound i) y ∘ bound)) := by
  induction h with
  | falsum =>
      exact ⟨CompactHilbertBasis.identity 1, CompactHilbertBasis.identity 1⟩
  | equal t u => exact scoped_equal_active_down t u bound i y hfree hdown
  | @imp a b ha hb iha ihb =>
      have hfa : bound i ∉ a.freeVarFinset := by
        intro h; apply hfree; simp [BoundedFormula.freeVarFinset, h]
      have hfb : bound i ∉ b.freeVarFinset := by
        intro h; apply hfree; simp [BoundedFormula.freeVarFinset, h]
      have aa := iha hfa
      have bb := ihb hfb
      change KBoth (.imp (replace (bound i) y (scopedFormula n a bound))
          (replace (bound i) y (scopedFormula n b bound)))
        (.imp (scopedFormula n a (rename (bound i) y ∘ bound))
          (scopedFormula n b (rename (bound i) y ∘ bound)))
      exact ⟨implicationCongr aa.2 bb.1, implicationCongr aa.1 bb.2⟩

end PASoundness.PAtoCompactScopedActiveDown

#print axioms PASoundness.PAtoCompactScopedActiveDown.scoped_equal_active_down
#print axioms PASoundness.PAtoCompactScopedActiveDown.scoped_qfree_active_down
