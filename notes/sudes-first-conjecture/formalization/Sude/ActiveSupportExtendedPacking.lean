import Sude.LayerPackingConcatenate
import Sude.LayerTranspose

/-! Extend joint layer reservations by the complement of a supplied active
physical support. This is a packing statement only. -/
namespace Sude.LayerPacking
noncomputable section

/-- If the active set contains the physical supports of both networks, their
existing normalized packings remain valid after every cell outside that set is
added to the reservation. The column support is transposed into physical
coordinates, and the column reservation retains the row support. -/
theorem packed_layers_extend_outside_active {n : ℕ}
    (reserved active : Finset (Cell n)) (rows cols : List (Layer n))
    (hrows : PackedLayers reserved rows)
    (hcols : PackedLayers (transposeCells (reserved ∪ layersSupport rows)) cols)
    (hrowActive : layersSupport rows ⊆ active)
    (hcolActive : transposeCells (layersSupport cols) ⊆ active) :
    PackedLayers (reserved ∪ (Finset.univ \ active)) rows ∧
    PackedLayers (transposeCells ((reserved ∪ (Finset.univ \ active)) ∪
      layersSupport rows)) cols := by
  classical
  have hrowDisjoint : Disjoint (Finset.univ \ active) (layersSupport rows) := by
    apply Finset.disjoint_left.mpr
    intro x hx hr
    exact (Finset.mem_sdiff.mp hx).2 (hrowActive hr)
  have hcolDisjoint : Disjoint (transposeCells (Finset.univ \ active))
      (layersSupport cols) := by
    apply Finset.disjoint_left.mpr
    intro x hx hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hyActive : y ∈ active := hcolActive (Finset.mem_image.mpr ⟨y.swap, hc, by simp⟩)
    exact (Finset.mem_sdiff.mp hy).2 hyActive
  refine ⟨hrows.extend_reservation hrowDisjoint, ?_⟩
  have hext := hcols.extend_reservation hcolDisjoint
  simpa [transposeCells, Finset.image_union, Finset.union_assoc,
    Finset.union_comm, Finset.union_left_comm] using hext

end
end Sude.LayerPacking
