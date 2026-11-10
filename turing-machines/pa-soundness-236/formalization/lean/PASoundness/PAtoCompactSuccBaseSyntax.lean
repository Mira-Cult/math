import PASoundness.PAtoCompactEquivStepsSyntax

/-! Literal mapping of the successor template's private names across
disjoint allocator blocks. This is a syntactic identity, not a K proof of
alpha-equivalence or a proof that individual renaming steps are safe. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccBaseSyntax

open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactMultiAlpha PASoundness.PAtoCompactGuardElimination
open PASoundness.PAtoCompactMapNamesCongr PASoundness.PAtoCompactEquivStepsSyntax

def succOffsets : List Nat := [2,3,4,5,6,7,8,19,20,21,22,30,31,32,33,34,35,36,37]

def succSteps (b c : Nat) : List (Nat × Nat) :=
  succOffsets.map (fun k => (b + 2 + k, c + 2 + k))

theorem succOffsets_lt (k : Nat) (hk : k ∈ succOffsets) : k < 38 := by
  simp [succOffsets] at hk
  omega

theorem succSteps_fix (b c z : Nat) (hz : z < b + 2) :
    applySteps (succSteps b c) z = z := by
  apply applySteps_avoid
  intro p hp
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
  simp only
  omega

theorem succSteps_hit (b c k : Nat) (hk : k ∈ succOffsets)
    (hdis : b + 39 < c + 2) :
    applySteps (succSteps b c) (b + 2 + k) = c + 2 + k := by
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
    have hjlt := succOffsets_lt j hj
    have hklt := succOffsets_lt k hk
    simp only
    omega

/-- Every named successor-template node is an input placeholder or one of
the explicitly listed private labels. -/
theorem successor_names_subset :
    successorTemplate.names ⊆ insert 0 (insert 1 succOffsets.toFinset) := by
  decide

/-- Simultaneously rename the listed successor-template labels, preserving
the two input names. Input names may be equal. -/
theorem renameSteps_succAt (b c x y : Nat)
    (hdis : b + 39 < c + 2) (hx : x < b + 2) (hy : y < b + 2) :
    renameSteps (succSteps b c) (succAt b x y) = succAt c x y := by
  rw [renameSteps_eq_map]
  unfold succAt
  rw [mapNames_compose]
  apply mapNames_congr
  intro z hz
  have hsupport := successor_names_subset hz
  simp only [Finset.mem_insert, List.mem_toFinset] at hsupport
  rcases hsupport with rfl | rfl | hk
  · simpa only [Function.comp_apply, twoMap, if_true] using succSteps_fix b c x hx
  · simpa only [Function.comp_apply, twoMap, Nat.reduceEqDiff, if_true, if_false] using succSteps_fix b c y hy
  · have hz0 : z ≠ 0 := by simp [succOffsets] at hk; omega
    have hz1 : z ≠ 1 := by simp [succOffsets] at hk; omega
    simpa only [Function.comp_apply, twoMap, hz0, hz1, if_false] using succSteps_hit b c z hk hdis

end PASoundness.PAtoCompactSuccBaseSyntax

#print axioms PASoundness.PAtoCompactSuccBaseSyntax.succOffsets_lt
#print axioms PASoundness.PAtoCompactSuccBaseSyntax.succSteps_fix
#print axioms PASoundness.PAtoCompactSuccBaseSyntax.succSteps_hit
#print axioms PASoundness.PAtoCompactSuccBaseSyntax.successor_names_subset
#print axioms PASoundness.PAtoCompactSuccBaseSyntax.renameSteps_succAt
