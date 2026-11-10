import PASoundness.PAtoCompactEquivStepsSyntax

/-! Literal mapping of the addition template's private names across disjoint
allocator blocks. This is syntax only: it does not prove that individual
renames are safe or supply a K proof of alpha equivalence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAddBaseSyntax

open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactMultiAlpha PASoundness.PAtoCompactGuardElimination
open PASoundness.PAtoCompactMapNamesCongr PASoundness.PAtoCompactEquivStepsSyntax

def addOffsets : List Nat := [2,3,4,5,6,19,20,21,22,33,34,35]

def addSteps (b c : Nat) : List (Nat × Nat) :=
  addOffsets.map (fun k => (b + 2 + k, c + 2 + k))

theorem addOffsets_lt (k : Nat) (hk : k ∈ addOffsets) : k < 38 := by
  simp [addOffsets] at hk
  omega

theorem addSteps_fix (b c z : Nat) (hz : z < b + 2) :
    applySteps (addSteps b c) z = z := by
  apply applySteps_avoid
  intro p hp
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
  simp only
  omega

theorem addSteps_hit (b c k : Nat) (hk : k ∈ addOffsets)
    (hdis : b + 39 < c + 2) :
    applySteps (addSteps b c) (b + 2 + k) = c + 2 + k := by
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
    have hjlt := addOffsets_lt j hj
    have hklt := addOffsets_lt k hk
    simp only
    omega

/-- Every named addition-template node is an input placeholder or one of
the listed private labels. -/
theorem addition_names_subset :
    (normalizeBottom additionFormula).names ⊆
      insert 30 (insert 31 (insert 32 addOffsets.toFinset)) := by
  decide

/-- Rename the listed addition-template labels while preserving all three
inputs, which may coincide. The two private blocks are disjoint. -/
theorem renameSteps_addAt (b c x y z : Nat)
    (hdis : b + 39 < c + 2) (hx : x < b + 2) (hy : y < b + 2)
    (hz : z < b + 2) :
    renameSteps (addSteps b c) (addAt b x y z) = addAt c x y z := by
  rw [renameSteps_eq_map]
  unfold addAt
  rw [mapNames_compose]
  apply mapNames_congr
  intro k hk
  have hsupport := addition_names_subset hk
  simp only [Finset.mem_insert, List.mem_toFinset] at hsupport
  rcases hsupport with rfl | rfl | rfl | hm
  · simpa only [Function.comp_apply, threeMap, if_true] using addSteps_fix b c x hx
  · simpa only [Function.comp_apply, threeMap, Nat.reduceEqDiff, if_true, if_false] using addSteps_fix b c y hy
  · simpa only [Function.comp_apply, threeMap, Nat.reduceEqDiff, if_true, if_false] using addSteps_fix b c z hz
  · have hk30 : k ≠ 30 := by simp [addOffsets] at hm; omega
    have hk31 : k ≠ 31 := by simp [addOffsets] at hm; omega
    have hk32 : k ≠ 32 := by simp [addOffsets] at hm; omega
    simpa only [Function.comp_apply, threeMap, hk30, hk31, hk32, if_false] using
      addSteps_hit b c k hm hdis

end PASoundness.PAtoCompactAddBaseSyntax

#print axioms PASoundness.PAtoCompactAddBaseSyntax.addOffsets_lt
#print axioms PASoundness.PAtoCompactAddBaseSyntax.addSteps_fix
#print axioms PASoundness.PAtoCompactAddBaseSyntax.addSteps_hit
#print axioms PASoundness.PAtoCompactAddBaseSyntax.addition_names_subset
#print axioms PASoundness.PAtoCompactAddBaseSyntax.renameSteps_addAt
