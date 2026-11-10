import PASoundness.PAtoCompactGeneralizationFreshAlpha
import PASoundness.PAtoCompactVacuousQuantifierFree
import PASoundness.PAtoCompactScopedAlphaInvariant

/-! Capture-safe replacement in actual finite K proof data. This supplies a
proof-transformation step for scoped active-name alignment; it does not yet
establish that alignment or the PA vacuous logical handler. -/
namespace PASoundness.PAtoCompactScopedActiveReplace

open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactGeneralizationFreshAlpha
open FirstOrder FirstOrder.Language
open PASoundness.PAtoCompactScopedEqualityReplace PASoundness.PAtoCompactVacuousQuantifierFree
open PASoundness.PAtoCompactScopedAlphaInvariant

/-- Generalize a finite K derivation and instantiate it at another name.
Both names must be absent from the formula's binder set; the equal-name case
uses literal identity. No semantic soundness theorem is used. -/
def replace_derivation (x y : Nat) (f : Formula)
    (hx : x ∉ f.binders) (hy : y ∉ f.binders) (d : KDerivation f.encode) :
    KDerivation (replace x y f).encode := by
  by_cases hxy : x = y
  · subst y
    simpa only [replace_self] using d
  · exact .mp (.generalize x d) (universalInstance x y f hxy hx hy)

/-- Apply the capture-safe proof transformer to both directions of a K
implication pair. This remains valid when the two new formulas share values. -/
def replace_implications (x y : Nat) (a b : Formula)
    (hxa : x ∉ a.binders) (hxb : x ∉ b.binders)
    (hya : y ∉ a.binders) (hyb : y ∉ b.binders)
    (forward : KDerivation (imp a.encode b.encode))
    (backward : KDerivation (imp b.encode a.encode)) :
    KDerivation (imp (replace x y a).encode (replace x y b).encode) ×
      KDerivation (imp (replace x y b).encode (replace x y a).encode) := by
  have hx : x ∉ (Formula.imp a b).binders := by
    simpa only [Formula.binders, Finset.mem_union, not_or] using And.intro hxa hxb
  have hy : y ∉ (Formula.imp a b).binders := by
    simpa only [Formula.binders, Finset.mem_union, not_or] using And.intro hya hyb
  have hx' : x ∉ (Formula.imp b a).binders := by
    simpa only [Formula.binders, Finset.mem_union, not_or] using And.intro hxb hxa
  have hy' : y ∉ (Formula.imp b a).binders := by
    simpa only [Formula.binders, Finset.mem_union, not_or] using And.intro hyb hya
  exact ⟨replace_derivation x y (.imp a b) hx hy forward,
    replace_derivation x y (.imp b a) hx' hy' backward⟩

theorem replace_derivation_certificate (x y : Nat) (f : Formula)
    (hx : x ∉ f.binders) (hy : y ∉ f.binders) (d : KDerivation f.encode) :
    theoremCode (certificate (replace_derivation x y f hx hy d)) = (replace x y f).encode :=
  certificate_correct _

/-- Equality frames depend on a name map only at variables occurring in the
two source terms. -/
theorem equalityFrame_name_agree {α : Type} [DecidableEq α]
    (t u : Peano.language.Term α) (f g : α → Nat) (base : Nat)
    (ht : ∀ v ∈ t.varFinset, f v = g v) (hu : ∀ v ∈ u.varFinset, f v = g v) :
    equalityFrame f t u base = equalityFrame g t u base := by
  unfold equalityFrame
  rw [termGraph_name_agree t f g ht, termGraph_name_agree u f g hu]

/-- First transport a frame with its original names, then replace an active
name in both finite K proofs. Unlike direct base transport, the replacement
target may lie above the old base as long as it is not an old binder. -/
noncomputable def equalityFrame_replace_base_transport {α : Type} [DecidableEq α]
    (v : α → Nat) (t u : Peano.language.Term α) (b c x y : Nat)
    (hxb : x < b) (hxc : x < c) (hyc : y < c)
    (hyb : y ∉ (equalityFrame v t u b).binders)
    (htb : ∀ a ∈ t.varFinset, v a < b) (hub : ∀ a ∈ u.varFinset, v a < b)
    (htc : ∀ a ∈ t.varFinset, v a < c) (huc : ∀ a ∈ u.varFinset, v a < c) :
    KBoth (equalityFrame (rename x y ∘ v) t u b)
      (equalityFrame (rename x y ∘ v) t u c) := by
  let A := equalityFrame v t u b
  let B := equalityFrame v t u c
  have hxa : x ∉ A.binders := target_not_bound v t u b x hxb
  have hxc' : x ∉ B.binders := target_not_bound v t u c x hxc
  have hyc' : y ∉ B.binders := target_not_bound v t u c y hyc
  have d := equalityFrame_base_transport v t u b c htb hub htc huc
  have r := replace_implications x y A B hxa hxc' hyb hyc' d.1 d.2
  simpa only [KBoth, A, B, replace_equalityFrame v t u b x y hxb,
    replace_equalityFrame v t u c x y hxc] using r

end PASoundness.PAtoCompactScopedActiveReplace

#print axioms PASoundness.PAtoCompactScopedActiveReplace.replace_derivation
#print axioms PASoundness.PAtoCompactScopedActiveReplace.replace_implications
#print axioms PASoundness.PAtoCompactScopedActiveReplace.replace_derivation_certificate
#print axioms PASoundness.PAtoCompactScopedActiveReplace.equalityFrame_name_agree
#print axioms PASoundness.PAtoCompactScopedActiveReplace.equalityFrame_replace_base_transport

namespace PASoundness.PAtoCompactScopedActiveReplace
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactScopedEqualityReplace PASoundness.PAtoCompactVacuousQuantifierFree
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactEqualityGraphTruth

theorem eq_left_name_lt {n : Nat} (t u : Peano.language.Term (Nat ⊕ Fin n))
    (bound : Fin n → Nat) (a : Nat ⊕ Fin n) (ha : a ∈ t.varFinset) :
    Sum.elim id bound a < scopeBase (.equal t u) bound := by
  have hsubset := term_image_subset t (.equal t u) bound
    (by intro x hx; exact Finset.mem_union_left _ hx)
  have hmem := hsubset (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  rcases Finset.mem_union.mp hmem with hfree | hb
  · exact free_lt_scopeBase (.equal t u) bound _ hfree
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hb
    rw [← hi]
    exact bound_lt_scopeBase (.equal t u) bound i

theorem eq_right_name_lt {n : Nat} (t u : Peano.language.Term (Nat ⊕ Fin n))
    (bound : Fin n → Nat) (a : Nat ⊕ Fin n) (ha : a ∈ u.varFinset) :
    Sum.elim id bound a < scopeBase (.equal t u) bound := by
  have hsubset := term_image_subset u (.equal t u) bound
    (by intro x hx; exact Finset.mem_union_right _ hx)
  have hmem := hsubset (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  rcases Finset.mem_union.mp hmem with hfree | hb
  · exact free_lt_scopeBase (.equal t u) bound _ hfree
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hb
    rw [← hi]
    exact bound_lt_scopeBase (.equal t u) bound i

/-- Active-bound replacement aligns an equality scope with the updated bound
environment when the replacement label is fresh in the old scope. -/
noncomputable def scoped_equal_active_replace {n : Nat}
    (t u : Peano.language.Term (Nat ⊕ Fin n)) (bound : Fin n → Nat) (i : Fin n) (w : Nat)
    (hfree : bound i ∉ (.equal t u : Peano.language.BoundedFormula Nat n).freeVarFinset)
    (hgt : bound i < w) (hw : w ∉ (scopedFormula n (.equal t u) bound).names) :
    KBoth (replace (bound i) w (scopedFormula n (.equal t u) bound))
      (scopedFormula n (.equal t u) (rename (bound i) w ∘ bound)) := by
  let a := bound i
  let v := Sum.elim id bound
  let bound' := rename a w ∘ bound
  let v' := Sum.elim id bound'
  let b := scopeBase (.equal t u) bound
  let c := scopeBase (.equal t u) bound'
  have hab : a < b := bound_lt_scopeBase (.equal t u) bound i
  have hwc : w < c := by
    have h := bound_lt_scopeBase (.equal t u) bound' i
    simpa [bound', rename, a] using h
  have hac : a < c := by omega
  have hwb : w ∉ (equalityFrame v t u b).binders := by
    intro hh
    have hh' : w ∈ (scopedFormula n (.equal t u) bound).binders := by
      simpa [scoped_equal_frame, v, b] using hh
    exact hw ((scopedFormula n (.equal t u) bound).binders_subset_names hh')
  have ht : ∀ z ∈ t.varFinset, rename a w (v z) = v' z := by
    intro z hz
    cases z with
    | inl x =>
        have hxf : x ∈ (.equal t u : Peano.language.BoundedFormula Nat n).freeVarFinset := by
          change x ∈ t.varFinsetLeft ∪ u.varFinsetLeft
          exact Finset.mem_union_left _ (inl_mem_left t x hz)
        have hxa : x ≠ a := by intro h; subst x; exact hfree hxf
        simp [v, v', rename, hxa]
    | inr j => rfl
  have hu : ∀ z ∈ u.varFinset, rename a w (v z) = v' z := by
    intro z hz
    cases z with
    | inl x =>
        have hxf : x ∈ (.equal t u : Peano.language.BoundedFormula Nat n).freeVarFinset := by
          change x ∈ t.varFinsetLeft ∪ u.varFinsetLeft
          exact Finset.mem_union_right _ (inl_mem_left u x hz)
        have hxa : x ≠ a := by intro h; subst x; exact hfree hxf
        simp [v, v', rename, hxa]
    | inr j => rfl
  have old_lt_target (z : Nat ⊕ Fin n) : v z ≤ v' z ∨ v z = v' z := by
    cases z with
    | inl x => right; rfl
    | inr j =>
        by_cases he : bound j = a
        · left; simp [v, v', bound', rename, he]; omega
        · right; simp [v, v', bound', rename, he]
  have htc : ∀ z ∈ t.varFinset, v z < c := by
    intro z hz
    have hh : v' z < c := eq_left_name_lt t u bound' z hz
    rcases old_lt_target z with hh' | hh' <;> omega
  have huc : ∀ z ∈ u.varFinset, v z < c := by
    intro z hz
    have hh : v' z < c := eq_right_name_lt t u bound' z hz
    rcases old_lt_target z with hh' | hh' <;> omega
  rw [scoped_equal_frame, scoped_equal_frame]
  rw [← equalityFrame_name_agree t u (rename a w ∘ v) v' c ht hu]
  rw [replace_equalityFrame v t u b a w hab]
  exact equalityFrame_replace_base_transport v t u b c a w hab hac hwc hwb
    (eq_left_name_lt t u bound) (eq_right_name_lt t u bound) htc huc
end PASoundness.PAtoCompactScopedActiveReplace
#print axioms PASoundness.PAtoCompactScopedActiveReplace.scoped_equal_active_replace

namespace PASoundness.PAtoCompactScopedActiveReplace
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactVacuousQuantifierFree

/-- Quantifier-free bounded PA formulas, with arbitrary active depth. -/
inductive ScopedQFree {n : Nat} : Peano.language.BoundedFormula Nat n → Type
  | falsum : ScopedQFree .falsum
  | equal (t u : Peano.language.Term (Nat ⊕ Fin n)) : ScopedQFree (.equal t u)
  | imp {a b} : ScopedQFree a → ScopedQFree b → ScopedQFree (.imp a b)

/-- At arbitrary scope depth, capture-safe replacement of an active label
commutes with updating the active-name environment, up to finite K proofs,
for formulas with no quantifiers. -/
noncomputable def scoped_qfree_active_replace {n : Nat}
    {φ : Peano.language.BoundedFormula Nat n} (h : ScopedQFree φ)
    (bound : Fin n → Nat) (i : Fin n) (w : Nat)
    (hfree : bound i ∉ φ.freeVarFinset) (hgt : bound i < w)
    (hw : w ∉ (scopedFormula n φ bound).names) :
    KBoth (replace (bound i) w (scopedFormula n φ bound))
      (scopedFormula n φ (rename (bound i) w ∘ bound)) := by
  induction h with
  | falsum =>
      exact ⟨CompactHilbertBasis.identity 1, CompactHilbertBasis.identity 1⟩
  | equal t u => exact scoped_equal_active_replace t u bound i w hfree hgt hw
  | @imp a b ha hb iha ihb =>
      have hfa : bound i ∉ a.freeVarFinset := by
        intro h; apply hfree; simp [BoundedFormula.freeVarFinset, h]
      have hfb : bound i ∉ b.freeVarFinset := by
        intro h; apply hfree; simp [BoundedFormula.freeVarFinset, h]
      have hwa : w ∉ (scopedFormula n a bound).names := by
        intro h; apply hw; simp [scopedFormula, Formula.names, h]
      have hwb : w ∉ (scopedFormula n b bound).names := by
        intro h; apply hw; simp [scopedFormula, Formula.names, h]
      have aa := iha hfa hwa
      have bb := ihb hfb hwb
      change KBoth (.imp (replace (bound i) w (scopedFormula n a bound))
          (replace (bound i) w (scopedFormula n b bound)))
        (.imp (scopedFormula n a (rename (bound i) w ∘ bound))
          (scopedFormula n b (rename (bound i) w ∘ bound)))
      exact ⟨implicationCongr aa.2 bb.1, implicationCongr aa.1 bb.2⟩

end PASoundness.PAtoCompactScopedActiveReplace
#print axioms PASoundness.PAtoCompactScopedActiveReplace.scoped_qfree_active_replace
