import PASoundness.PAtoCompactMultiAlpha
import PASoundness.PAtoCompactGuardElimination
import PASoundness.PAtoCompactMapNamesCongr

/-! Literal identification of the nine-step private-name mapping of the
quotient-equivalence template. This file does not prove the alpha-step side
conditions or K equivalence of the two formulas. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactEquivStepsSyntax

open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactMultiAlpha
open PASoundness.PAtoCompactGuardElimination PASoundness.PAtoCompactMapNamesCongr

def offsets : List Nat := [2,3,4,5,6,19,20,21,22]

def equivSteps (b c : Nat) : List (Nat × Nat) :=
  offsets.map (fun k => (b+2+k,c+2+k))

def applySteps : List (Nat × Nat) → Nat → Nat
  | [], z => z
  | (a,b) :: rest, z => applySteps rest (rename a b z)

theorem applySteps_avoid (steps : List (Nat × Nat)) (z : Nat)
    (h : ∀ p ∈ steps, p.1 ≠ z) : applySteps steps z = z := by
  induction steps with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨a,b⟩ := p
      have ha : a ≠ z := h (a,b) (by simp)
      have ht : ∀ p ∈ rest, p.1 ≠ z := by intro p hp; exact h p (by simp [hp])
      simpa [applySteps, rename, Ne.symm ha] using ih ht

theorem applySteps_hit (steps : List (Nat × Nat)) (x y : Nat)
    (hmem : (x,y) ∈ steps)
    (hunique : ∀ z, (x,z) ∈ steps → z = y)
    (havoid : ∀ p ∈ steps, p.1 ≠ y) : applySteps steps x = y := by
  induction steps with
  | nil => simp at hmem
  | cons p rest ih =>
      obtain ⟨a,b⟩ := p
      have ht : ∀ p ∈ rest, p.1 ≠ y := by intro p hp; exact havoid p (by simp [hp])
      by_cases he : a = x
      · subst a
        have hb : b = y := hunique b (by simp)
        subst b
        simpa [applySteps, rename] using applySteps_avoid rest y ht
      · have hm : (x,y) ∈ rest := by simpa [Ne.symm he] using hmem
        have hu : ∀ z, (x,z) ∈ rest → z = y := by
          intro z hz; exact hunique z (by simp [hz])
        simpa [applySteps, rename, Ne.symm he] using ih hm hu ht

theorem offsets_lt (k : Nat) (hk : k ∈ offsets) : k < 38 := by
  simp [offsets] at hk
  omega

theorem equivSteps_fix (b c z : Nat) (hz : z < b + 2) :
    applySteps (equivSteps b c) z = z := by
  apply applySteps_avoid
  intro p hp
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
  simp only
  omega

theorem equivSteps_hit (b c k : Nat) (hk : k ∈ offsets) (hdis : b + 39 < c + 2) :
    applySteps (equivSteps b c) (b + 2 + k) = c + 2 + k := by
  apply applySteps_hit
  · apply List.mem_map.mpr
    exact ⟨k, hk, rfl⟩
  · intro z hz
    obtain ⟨j, hj, he⟩ := List.mem_map.mp hz
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    simp only at h1 h2
    omega
  · intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    have hjlt := offsets_lt j hj
    have hklt := offsets_lt k hk
    simp only
    omega

theorem renameSteps_eq_map (steps : List (Nat × Nat)) (f : Formula) :
    renameSteps steps f = mapNames (applySteps steps) f := by
  induction steps generalizing f with
  | nil =>
      change f = mapNames id f
      exact (mapNames_id f).symm
  | cons p rest ih =>
      obtain ⟨a,b⟩ := p
      rw [renameSteps, ih, mapNames_compose]
      rfl

theorem equiv_template_name_cases :
    (normalizeBottom equivalentFormula).names ⊆
      ({0,1,2,3,4,5,6,19,20,21,22} : Finset Nat) := by decide

/-- With disjoint blocks and operands below the source block, the final
syntactic result is exactly the same template allocated at the target base.
The two operands may be the same name. -/
theorem renameSteps_equivAt (b c x y : Nat)
    (hdis : b + 39 < c + 2) (hx : x < b + 2) (hy : y < b + 2) :
    renameSteps (equivSteps b c) (equivAt b x y) = equivAt c x y := by
  rw [renameSteps_eq_map]
  unfold equivAt
  rw [mapNames_compose]
  apply mapNames_congr
  intro z hz
  have hcases := equiv_template_name_cases hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcases
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [Function.comp_apply, twoMap, if_true] using equivSteps_fix b c x hx
  · simpa only [Function.comp_apply, twoMap, Nat.reduceEqDiff, if_true, if_false] using equivSteps_fix b c y hy
  · simpa only [Function.comp_apply, twoMap, Nat.reduceEqDiff, if_false] using equivSteps_hit b c 2 (by decide) hdis
  · simpa only [Function.comp_apply, twoMap, Nat.reduceEqDiff, if_false] using equivSteps_hit b c 3 (by decide) hdis
  · simpa only [Function.comp_apply, twoMap, Nat.reduceEqDiff, if_false] using equivSteps_hit b c 4 (by decide) hdis
  · simpa only [Function.comp_apply, twoMap, Nat.reduceEqDiff, if_false] using equivSteps_hit b c 5 (by decide) hdis
  · simpa only [Function.comp_apply, twoMap, Nat.reduceEqDiff, if_false] using equivSteps_hit b c 6 (by decide) hdis
  · simpa only [Function.comp_apply, twoMap, Nat.reduceEqDiff, if_false] using equivSteps_hit b c 19 (by decide) hdis
  · simpa only [Function.comp_apply, twoMap, Nat.reduceEqDiff, if_false] using equivSteps_hit b c 20 (by decide) hdis
  · simpa only [Function.comp_apply, twoMap, Nat.reduceEqDiff, if_false] using equivSteps_hit b c 21 (by decide) hdis
  · simpa only [Function.comp_apply, twoMap, Nat.reduceEqDiff, if_false] using equivSteps_hit b c 22 (by decide) hdis

end PASoundness.PAtoCompactEquivStepsSyntax

#print axioms PASoundness.PAtoCompactEquivStepsSyntax.renameSteps_eq_map
#print axioms PASoundness.PAtoCompactEquivStepsSyntax.applySteps_avoid
#print axioms PASoundness.PAtoCompactEquivStepsSyntax.applySteps_hit
#print axioms PASoundness.PAtoCompactEquivStepsSyntax.offsets_lt
#print axioms PASoundness.PAtoCompactEquivStepsSyntax.equivSteps_fix
#print axioms PASoundness.PAtoCompactEquivStepsSyntax.equivSteps_hit
#print axioms PASoundness.PAtoCompactEquivStepsSyntax.equiv_template_name_cases
#print axioms PASoundness.PAtoCompactEquivStepsSyntax.renameSteps_equivAt
