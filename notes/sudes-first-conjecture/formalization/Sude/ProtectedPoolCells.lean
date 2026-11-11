import Sude.ActualUnusedPool
import Sude.ScreenedPool

/-! Locate exactly the prescribed pool values protected by a finite set. -/
namespace Sude
noncomputable section

/-- The original cells whose entries belong to `values`. Values outside the
prescribed pool have no corresponding cell. -/
def protectedPoolCells {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (values : Finset ℕ) : Finset (Cell n) :=
  Finset.univ.filter fun c => entry a c ∈ values

@[simp] theorem mem_protectedPoolCells {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (values : Finset ℕ) (c : Cell n) :
    c ∈ protectedPoolCells a values ↔ entry a c ∈ values := by
  simp [protectedPoolCells]

/-- The image is exactly the supplied values that actually occur in the
prescribed pool, even when the supplied set contains non-pool numbers. -/
theorem protectedPoolCells_image {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (values : Finset ℕ) :
    (protectedPoolCells a values).image (entry a) = values ∩ poolFinset n := by
  ext p
  constructor
  · intro hp
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_inter.mpr ⟨(mem_protectedPoolCells a values c).mp hc,
      mem_poolFinset.mpr ⟨a c, rfl⟩⟩
  · intro hp
    obtain ⟨hv, hpool⟩ := Finset.mem_inter.mp hp
    have hrange : p ∈ Set.range (entry a) := by
      rw [entry_range a]
      exact mem_poolFinset.mp hpool
    obtain ⟨c, rfl⟩ := hrange
    exact Finset.mem_image.mpr ⟨c, (mem_protectedPoolCells a values c).mpr hv, rfl⟩

/-- Injectivity makes the number of protected cells exact. -/
theorem protectedPoolCells_card {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (values : Finset ℕ) :
    (protectedPoolCells a values).card = (values ∩ poolFinset n).card := by
  have h := congrArg Finset.card (protectedPoolCells_image a values)
  rw [Finset.card_image_of_injective _ (entry_injective a)] at h
  exact h

/-- If every supplied value belongs to the pool, each has a unique protected
cell, and the full image and cardinality equal the supplied finite set. -/
theorem protectedPoolCells_of_subset {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (values : Finset ℕ) (hpool : values ⊆ poolFinset n) :
    (protectedPoolCells a values).image (entry a) = values ∧
    (protectedPoolCells a values).card = values.card := by
  have hinter : values ∩ poolFinset n = values := Finset.inter_eq_left.mpr hpool
  exact ⟨(protectedPoolCells_image a values).trans hinter, by
    rw [protectedPoolCells_card, hinter]⟩

/-- Fixing protected cells preserves each supplied pool value at its exact
original position. The separate pool-membership premise is necessary for an
arbitrary set of natural values. -/
theorem protectedPoolCells_preserve_value {n : ℕ}
    (a b : Cell n ≃ Fin (n * n)) (values : Finset ℕ) (p : ℕ)
    (hp : p ∈ values) (hpool : p ∈ pool n)
    (hfixed : ∀ c ∈ protectedPoolCells a values, entry b c = entry a c) :
    entry b ((entryPool a).symm ⟨p, hpool⟩) = p := by
  let c := (entryPool a).symm ⟨p, hpool⟩
  have hc : entry a c = p := by
    change (entryPool a ((entryPool a).symm ⟨p, hpool⟩)).val = p
    rw [(entryPool a).apply_symm_apply]
  have hmem : c ∈ protectedPoolCells a values := (mem_protectedPoolCells a values c).mpr (hc ▸ hp)
  exact (hfixed c hmem).trans hc

end
end Sude
