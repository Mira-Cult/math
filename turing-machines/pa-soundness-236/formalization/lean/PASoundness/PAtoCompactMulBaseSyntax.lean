import PASoundness.PAtoCompactEquivStepsSyntax

/-! Literal mapping of the multiplication template's private names across
disjoint allocator blocks. This is a syntactic identity, not a K proof of
alpha-equivalence or a proof that individual renaming steps are safe. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMulBaseSyntax

open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactMultiAlpha PASoundness.PAtoCompactGuardElimination
open PASoundness.PAtoCompactMapNamesCongr PASoundness.PAtoCompactEquivStepsSyntax

def mulOffsets : List Nat := [3,4,5,6,7,8,9,18,19,20,21,22]

def mulSteps (b c : Nat) : List (Nat × Nat) :=
  mulOffsets.map (fun k => (b + 2 + k, c + 2 + k))

theorem mulOffsets_lt (k : Nat) (hk : k ∈ mulOffsets) : k < 38 := by
  simp [mulOffsets] at hk
  omega

theorem mulSteps_fix (b c z : Nat) (hz : z < b + 2) :
    applySteps (mulSteps b c) z = z := by
  apply applySteps_avoid
  intro p hp
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
  simp only
  omega

theorem mulSteps_hit (b c k : Nat) (hk : k ∈ mulOffsets)
    (hdis : b + 39 < c + 2) :
    applySteps (mulSteps b c) (b + 2 + k) = c + 2 + k := by
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
    have hjlt := mulOffsets_lt j hj
    have hklt := mulOffsets_lt k hk
    simp only
    omega

/-- Every named multiplication-template node is an input placeholder or one
of the explicitly listed private labels. -/
theorem product_names_subset :
    (normalizeBottom productFormula).names ⊆ insert 0 (insert 1 (insert 2 mulOffsets.toFinset)) := by
  decide

/-- Simultaneously rename the listed multiplication-template labels,
preserving the three input names. Input names may be equal. -/
theorem renameSteps_mulAt (b c x y z : Nat)
    (hdis : b + 39 < c + 2) (hx : x < b + 2) (hy : y < b + 2) (hz : z < b + 2) :
    renameSteps (mulSteps b c) (mulAt b x y z) = mulAt c x y z := by
  rw [renameSteps_eq_map]
  unfold mulAt
  rw [mapNames_compose]
  apply mapNames_congr
  intro w hw
  have hsupport := product_names_subset hw
  simp only [Finset.mem_insert, List.mem_toFinset] at hsupport
  rcases hsupport with rfl | rfl | rfl | hk
  · simpa only [Function.comp_apply, threeMap, if_true] using mulSteps_fix b c x hx
  · simpa only [Function.comp_apply, threeMap, Nat.reduceEqDiff, if_true, if_false] using mulSteps_fix b c y hy
  · simpa only [Function.comp_apply, threeMap, Nat.reduceEqDiff, if_true, if_false] using mulSteps_fix b c z hz
  · have hw0 : w ≠ 0 := by simp [mulOffsets] at hk; omega
    have hw1 : w ≠ 1 := by simp [mulOffsets] at hk; omega
    have hw2 : w ≠ 2 := by simp [mulOffsets] at hk; omega
    simpa only [Function.comp_apply, threeMap, hw0, hw1, hw2, if_false] using mulSteps_hit b c w hk hdis

end PASoundness.PAtoCompactMulBaseSyntax

#print axioms PASoundness.PAtoCompactMulBaseSyntax.mulOffsets_lt
#print axioms PASoundness.PAtoCompactMulBaseSyntax.mulSteps_fix
#print axioms PASoundness.PAtoCompactMulBaseSyntax.mulSteps_hit
#print axioms PASoundness.PAtoCompactMulBaseSyntax.product_names_subset
#print axioms PASoundness.PAtoCompactMulBaseSyntax.renameSteps_mulAt
