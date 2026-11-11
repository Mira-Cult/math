import Sude.PackedTradeSupportAgreement
import Sude.PackedRectangleLoads

/-! The cells in any selected set of packed rectangles belong to the full
packed rectangle support. No placement or diagonal-grid fact is asserted. -/
namespace Sude
noncomputable section

/-- A labelled subfamily uses only cells of the same packed rectangle family. -/
theorem packed_label_support_subset_rectangle_support {L n : ℕ}
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool) (labels : Finset (Fin L)) :
    packedLabelSupport hs choice labels ⊆ packedRectangleSupport hs choice := by
  classical
  intro z hz
  obtain ⟨i, _, hz⟩ := Finset.mem_biUnion.mp hz
  rcases (mem_rectangleCells _ _ _ _ _).mp hz with h | h | h | h
  · subst z
    exact Finset.mem_image.mpr ⟨(i, 0), Finset.mem_univ _, rfl⟩
  · subst z
    exact Finset.mem_image.mpr ⟨(i, 1), Finset.mem_univ _, rfl⟩
  · subst z
    exact Finset.mem_image.mpr ⟨(i, 2), Finset.mem_univ _, rfl⟩
  · subst z
    exact Finset.mem_image.mpr ⟨(i, 3), Finset.mem_univ _, rfl⟩

end
end Sude
