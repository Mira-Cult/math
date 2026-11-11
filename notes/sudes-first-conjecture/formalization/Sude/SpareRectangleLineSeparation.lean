import Sude.ActiveRectangleLineCounts
import Sude.FWActiveRectangleLabels

/-! Row and column separation for disjoint rectangle-label families. This
does not estimate cell values or make a diagonal claim. -/
namespace Sude
noncomputable section

/-- Corners belonging to disjoint label families cannot share a row or a
column. All four sides of every supplied label are allowed. -/
theorem disjoint_rectangle_labels_separate_lines {L n : ℕ}
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (active spare : Finset (Fin L)) (hdisj : Disjoint active spare) :
    ∀ x ∈ activeRectangleSupport hs choice active,
      ∀ y ∈ activeRectangleSupport hs choice spare, x.1 ≠ y.1 ∧ x.2 ≠ y.2 := by
  classical
  intro x hx y hy
  obtain ⟨⟨i, s⟩, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨⟨j, t⟩, hj, rfl⟩ := Finset.mem_image.mp hy
  have hi' : i ∈ active := (Finset.mem_product.mp hi).1
  have hj' : j ∈ spare := (Finset.mem_product.mp hj).1
  have hne : i ≠ j := by
    intro h
    subst j
    exact Finset.disjoint_left.mp hdisj hi' hj'
  exact ⟨fun he => hne (packedCorner_row_label hs choice i j s t he),
    fun he => hne (packedCorner_column_label hs choice i j s t he)⟩

/-- The full rectangle support minus the active rectangles is exactly the
support of the complementary label set. -/
theorem packed_rectangle_support_sdiff_active {L n : ℕ}
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool) (active : Finset (Fin L)) :
    packedRectangleSupport hs choice \ activeRectangleSupport hs choice active =
      activeRectangleSupport hs choice (Finset.univ \ active) := by
  classical
  have hprod : ((Finset.univ : Finset (Fin L)) ×ˢ (Finset.univ : Finset (Fin 4))) \
      (active ×ˢ (Finset.univ : Finset (Fin 4))) =
      ((Finset.univ \ active) ×ˢ (Finset.univ : Finset (Fin 4))) := by
    ext ⟨i, s⟩
    simp
  have hall : ((Finset.univ : Finset (Fin L)) ×ˢ (Finset.univ : Finset (Fin 4))) =
      (Finset.univ : Finset (Fin L × Fin 4)) := by ext ⟨i, s⟩; simp
  unfold packedRectangleSupport activeRectangleSupport
  rw [← hall, ← Finset.image_sdiff _ _ (packedRectangleCorner_injective hs choice), hprod]

/-- FW's active and spare label corners have disjoint row and column
projections; each spare row or column contains zero or two spare corners.
The final identity identifies the spare corners with the rectangle-support
difference used by the full-reservation geometry. -/
theorem fw_spare_rectangle_line_separation {n P : ℕ} (hP : P ≤ 238)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool) :
    (∀ x ∈ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP),
      ∀ y ∈ activeRectangleSupport hs choice (fwSpareRectangleLabels n P hP),
        x.1 ≠ y.1 ∧ x.2 ≠ y.2) ∧
    (∀ r, (LayerPacking.rowUsed (activeRectangleSupport hs choice (fwSpareRectangleLabels n P hP)) r).card = 0 ∨
      (LayerPacking.rowUsed (activeRectangleSupport hs choice (fwSpareRectangleLabels n P hP)) r).card = 2) ∧
    (∀ c, (LayerPacking.colUsed (activeRectangleSupport hs choice (fwSpareRectangleLabels n P hP)) c).card = 0 ∨
      (LayerPacking.colUsed (activeRectangleSupport hs choice (fwSpareRectangleLabels n P hP)) c).card = 2) ∧
    packedRectangleSupport hs choice \ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP) =
      activeRectangleSupport hs choice (fwSpareRectangleLabels n P hP) := by
  have hdisj : Disjoint (fwActiveRectangleLabels n P hP) (fwSpareRectangleLabels n P hP) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 hx
  refine ⟨disjoint_rectangle_labels_separate_lines hs choice _ _ hdisj, ?_, ?_, ?_⟩
  · exact active_rectangle_row_count hs choice _
  · exact active_rectangle_column_count hs choice _
  · exact packed_rectangle_support_sdiff_active hs choice _

end
end Sude
