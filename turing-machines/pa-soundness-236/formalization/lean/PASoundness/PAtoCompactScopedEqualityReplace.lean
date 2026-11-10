import PASoundness.PAtoCompactTermGraphReplace
import PASoundness.PAtoCompactFormulaTranslation

/-! Literal replacement for one translated equality node with its allocated
base fixed. This is syntax, not K equivalence between different free names. -/
namespace PASoundness.PAtoCompactScopedEqualityReplace

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactMapNamesCongr
open PASoundness.PAtoCompactTemplateBlockShift PASoundness.PAtoCompactTermGraphBlockShift
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactAlphaMapOne

/-- The exact existential frame generated for a source equality. -/
def equalityFrame {α : Type} (v : α → Nat) (t u : Peano.language.Term α) (base : Nat) : Formula :=
  .ex base (.ex (base + 1)
    (andF (termGraph v t base (base + 2))
      (andF (termGraph v u (base + 1) (base + 2 + termCost t))
        (equivAt (base + 2 + termCost t + termCost u) base (base + 1)))))

theorem scoped_equal_frame {n : Nat} (t u : Peano.language.Term (Nat ⊕ Fin n))
    (bound : Fin n → Nat) :
    scopedFormula n (.equal t u) bound =
      equalityFrame (Sum.elim id bound) t u (scopeBase (.equal t u) bound) := by
  rfl

/-- Every bound name in the equality frame is at least its allocation base. -/
theorem equalityFrame_binders_ge {α : Type} (v : α → Nat)
    (t u : Peano.language.Term α) (base w : Nat)
    (h : w ∈ (equalityFrame v t u base).binders) : base ≤ w := by
  simp only [equalityFrame, Formula.binders, andF_binders, Finset.mem_insert,
    Finset.mem_union] at h
  rcases h with rfl | rfl | ht | hu | he
  · omega
  · omega
  · have hh := termGraph_binder_range v t base (base + 2) w ht; omega
  · have hh := termGraph_binder_range v u (base + 1) (base + 2 + termCost t) w hu; omega
  · have hh := equivAt_private (base + 2 + termCost t + termCost u) base (base + 1) w he
    omega

/-- Renaming a name below the base commutes with construction of an equality
frame, with the new source-name map explicitly recorded. -/
theorem map_equalityFrame {α : Type} (v : α → Nat)
    (t u : Peano.language.Term α) (base x y : Nat) (hx : x < base) :
    mapNames (rename x y) (equalityFrame v t u base) =
      equalityFrame (rename x y ∘ v) t u base := by
  have hfix (z : Nat) (hz : base ≤ z) : rename x y z = z := by
    simp [rename, show z ≠ x by omega]
  have hshift (b size : Nat) (hb : base ≤ b) :
      BlockShift (rename x y) b b size := by
    intro i hi
    exact hfix (b + i) (by omega)
  have ht := termGraph_shift (rename x y) v t base (base + 2) (base + 2)
    (hshift _ _ (by omega))
  have hu := termGraph_shift (rename x y) v u (base + 1)
    (base + 2 + termCost t) (base + 2 + termCost t) (hshift _ _ (by omega))
  have he := equivAt_shift (rename x y) (base + 2 + termCost t + termCost u)
    (base + 2 + termCost t + termCost u) base (base + 1) (hshift _ _ (by omega))
  have hf0 : rename x y base = base := hfix base (by omega)
  have hf1 : rename x y (base + 1) = base + 1 := hfix (base + 1) (by omega)
  simpa only [equalityFrame, mapNames, mapNames_andF, hf0, hf1] using
    congrArg₂ (fun a b => Formula.ex base (Formula.ex (base + 1) (andF a b))) ht
      (congrArg₂ andF hu he)

/-- Named replacement has the same literal effect as updating the equality
frame's source-name map, provided the replaced name is below the allocator. -/
theorem replace_equalityFrame {α : Type} (v : α → Nat)
    (t u : Peano.language.Term α) (base x y : Nat) (hx : x < base) :
    replace x y (equalityFrame v t u base) = equalityFrame (rename x y ∘ v) t u base := by
  have hb : x ∉ (equalityFrame v t u base).binders := by
    intro h
    have := equalityFrame_binders_ge v t u base x h
    omega
  rw [← map_eq_replace x y _ hb]
  exact map_equalityFrame v t u base x y hx

/-- A target below the base is also absent from the equality frame's binders. -/
theorem target_not_bound {α : Type} (v : α → Nat)
    (t u : Peano.language.Term α) (base y : Nat) (hy : y < base) :
    y ∉ (equalityFrame v t u base).binders := by
  intro h
  have := equalityFrame_binders_ge v t u base y h
  omega

/-- The replacement law for the actual `scopedFormula` equality node. Its
allocation base is held fixed; no claim is made about the base chosen for a
separately relabeled source formula. -/
theorem replace_scoped_equal {n : Nat} (t u : Peano.language.Term (Nat ⊕ Fin n))
    (bound : Fin n → Nat) (x y : Nat) (hx : x < scopeBase (.equal t u) bound) :
    replace x y (scopedFormula n (.equal t u) bound) =
      equalityFrame (rename x y ∘ Sum.elim id bound) t u (scopeBase (.equal t u) bound) := by
  rw [scoped_equal_frame]
  exact replace_equalityFrame _ t u _ x y hx

end PASoundness.PAtoCompactScopedEqualityReplace

#print axioms PASoundness.PAtoCompactScopedEqualityReplace.scoped_equal_frame
#print axioms PASoundness.PAtoCompactScopedEqualityReplace.equalityFrame_binders_ge
#print axioms PASoundness.PAtoCompactScopedEqualityReplace.map_equalityFrame
#print axioms PASoundness.PAtoCompactScopedEqualityReplace.replace_equalityFrame
#print axioms PASoundness.PAtoCompactScopedEqualityReplace.target_not_bound
#print axioms PASoundness.PAtoCompactScopedEqualityReplace.replace_scoped_equal
