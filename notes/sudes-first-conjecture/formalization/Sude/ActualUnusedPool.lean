import Sude.FinitePopulationPlacement

/-! The exact remaining prescribed pool after reserving physical cells. -/
namespace Sude
noncomputable section

def entryPool {n : ℕ} (a : Cell n ≃ Fin (n * n)) : Cell n ≃ pool n :=
  a.trans (poolEquiv n)

@[simp] theorem entryPool_val {n : ℕ} (a : Cell n ≃ Fin (n * n)) (z : Cell n) :
    (entryPool a z).val = entry a z := rfl

/-- The exact values in cells not yet reserved; no new pool is chosen. -/
def actualUnusedPool {n : ℕ} (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n)) :
    Finset (pool n) := (Finset.univ \ reserved).image (entryPool a)

theorem mem_actualUnusedPool {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (v : pool n) :
    v ∈ actualUnusedPool a reserved ↔ ∀ z ∈ reserved, v.val ≠ entry a z := by
  classical
  constructor
  · intro hv z hz heq
    obtain ⟨w, hw, hew⟩ := Finset.mem_image.mp hv
    have hnot : w ∉ reserved := (Finset.mem_sdiff.mp hw).2
    have hvals : entry a w = entry a z := by
      have hvw := congrArg Subtype.val hew
      simpa using hvw.trans heq
    exact hnot ((entry_injective a hvals) ▸ hz)
  · intro hav
    let z := (entryPool a).symm v
    have he : entryPool a z = v := (entryPool a).apply_symm_apply v
    have hz : z ∉ reserved := by
      intro hzr
      apply hav z hzr
      have := congrArg Subtype.val he
      simpa using this.symm
    exact Finset.mem_image.mpr ⟨z, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hz⟩, he⟩

theorem actualUnusedPool_avoids {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) :
    ∀ v ∈ actualUnusedPool a reserved, ∀ z ∈ reserved, v.val ≠ entry a z := by
  intro v hv
  exact (mem_actualUnusedPool a reserved v).1 hv

/-- The remaining count is exact, not a numerical estimate. -/
theorem actualUnusedPool_card (n : ℕ) (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) :
    (actualUnusedPool a reserved).card + reserved.card = n * n := by
  classical
  unfold actualUnusedPool
  rw [Finset.card_image_of_injective _ (entryPool a).injective]
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ reserved)
  simpa [Fintype.card_prod] using h

/-- After placing precisely `selected` into `new` and preserving the old
reservation, the new unused pool is exactly the old one with those values
deleted. This includes every value and cannot lose multiplicity. -/
theorem actualUnusedPool_after_placement {n : ℕ} (a b : Cell n ≃ Fin (n * n))
    (reserved new : Finset (Cell n)) (selected : Finset (pool n))
    (hfixed : ∀ z ∈ reserved, entry b z = entry a z)
    (himage : new.image (entry b) = selected.image Subtype.val) :
    actualUnusedPool b (reserved ∪ new) = actualUnusedPool a reserved \ selected := by
  classical
  ext v
  rw [Finset.mem_sdiff, mem_actualUnusedPool, mem_actualUnusedPool]
  constructor
  · intro hv
    refine ⟨?_, ?_⟩
    · intro z hz
      rw [← hfixed z hz]
      exact hv z (Finset.mem_union_left _ hz)
    · intro hs
      have hm : v.val ∈ new.image (entry b) := by
        rw [himage]
        exact Finset.mem_image.mpr ⟨v, hs, rfl⟩
      obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hm
      exact hv z (Finset.mem_union_right _ hz) he.symm
  · rintro ⟨hold, hnot⟩ z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rw [hfixed z hz]
      exact hold z hz
    · intro he
      have hm : entry b z ∈ selected.image Subtype.val := by
        rw [← himage]
        exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
      obtain ⟨w, hw, hew⟩ := Finset.mem_image.mp hm
      have hvw : v = w := Subtype.ext (he.trans hew.symm)
      exact hnot (hvw ▸ hw)

end
end Sude
