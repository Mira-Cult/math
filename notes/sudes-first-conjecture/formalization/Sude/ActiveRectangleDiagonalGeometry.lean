import Sude.ActiveRectangleLineCounts
import Sude.FWFullDiagonalOverlap

/-! Exact diagonal cells and cardinalities for any supplied rectangle labels. -/
namespace Sude
noncomputable section

/-- The selected rectangles meet the main diagonal exactly in the designated
corner of each true-choice label. -/
theorem active_rectangle_main_cells {L n : ℕ} (hs : 2*L+1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (labels : Finset (Fin L)) :
    activeRectangleSupport hs choice labels ∩ mainCells n =
      (labels.filter fun i => choice i = true).image (fun i => packedRectangleCorner hs choice (i,0)) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨ha, hd⟩ := Finset.mem_inter.mp hz
    obtain ⟨⟨i,s⟩, hi, he⟩ := Finset.mem_image.mp ha
    have hil : i ∈ labels := (Finset.mem_product.mp hi).1
    have hd' : packedRectangleCorner hs choice (i,s) ∈ mainCells n := he ▸ hd
    have hside : s = 0 := by
      have h1 := (RectanglePacking.firstRow_secondColumn_off_diagonals hs hL choice i).1
      have h2 := (RectanglePacking.secondRow_firstColumn_off_diagonals hs hL choice i).1
      have h3 := (RectanglePacking.secondRow_secondColumn_off_diagonals hs hL choice i).1
      fin_cases s
      · rfl
      · exfalso; exact h1 (by simpa [packedRectangleCorner] using hd')
      · exfalso; exact h2 (by simpa [packedRectangleCorner] using hd')
      · exfalso; exact h3 (by simpa [packedRectangleCorner] using hd')
    subst s
    have hc : choice i = true := by
      cases h : choice i
      · have hh := (RectanglePacking.designated_corner_geometry hs choice i).2 h
        have : (RectanglePacking.firstRow hs i, RectanglePacking.firstColumn hs choice i) ∈ mainCells n := by
          simpa [packedRectangleCorner] using hd'
        exact (hh.2 this).elim
      · rfl
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hil,hc⟩, he⟩
  · intro hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hil,hc⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_inter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(i,0), Finset.mem_product.mpr ⟨hil, Finset.mem_univ _⟩, rfl⟩
    · simpa [packedRectangleCorner] using ((RectanglePacking.designated_corner_geometry hs choice i).1 hc).1

/-- The selected rectangles meet the anti-diagonal exactly in the designated
corner of each false-choice label. -/
theorem active_rectangle_anti_cells {L n : ℕ} (hs : 2*L+1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (labels : Finset (Fin L)) :
    activeRectangleSupport hs choice labels ∩ antiCells n =
      (labels.filter fun i => choice i = false).image (fun i => packedRectangleCorner hs choice (i,0)) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨ha, hd⟩ := Finset.mem_inter.mp hz
    obtain ⟨⟨i,s⟩, hi, he⟩ := Finset.mem_image.mp ha
    have hil : i ∈ labels := (Finset.mem_product.mp hi).1
    have hd' : packedRectangleCorner hs choice (i,s) ∈ antiCells n := he ▸ hd
    have hside : s = 0 := by
      have h1 := (RectanglePacking.firstRow_secondColumn_off_diagonals hs hL choice i).2
      have h2 := (RectanglePacking.secondRow_firstColumn_off_diagonals hs hL choice i).2
      have h3 := (RectanglePacking.secondRow_secondColumn_off_diagonals hs hL choice i).2
      fin_cases s
      · rfl
      · exfalso; exact h1 (by simpa [packedRectangleCorner] using hd')
      · exfalso; exact h2 (by simpa [packedRectangleCorner] using hd')
      · exfalso; exact h3 (by simpa [packedRectangleCorner] using hd')
    subst s
    have hc : choice i = false := by
      cases h : choice i
      · rfl
      · have hh := (RectanglePacking.designated_corner_geometry hs choice i).1 h
        have : (RectanglePacking.firstRow hs i, RectanglePacking.firstColumn hs choice i) ∈ antiCells n := by
          simpa [packedRectangleCorner] using hd'
        exact (hh.2 this).elim
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hil,hc⟩, he⟩
  · intro hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hil,hc⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_inter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(i,0), Finset.mem_product.mpr ⟨hil, Finset.mem_univ _⟩, rfl⟩
    · simpa [packedRectangleCorner] using ((RectanglePacking.designated_corner_geometry hs choice i).2 hc).1

/-- Their exact cardinalities are the respective numbers of selected labels. -/
theorem active_rectangle_diagonal_cards {L n : ℕ} (hs : 2*L+1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (labels : Finset (Fin L)) :
    (activeRectangleSupport hs choice labels ∩ mainCells n).card =
      (labels.filter fun i => choice i = true).card ∧
    (activeRectangleSupport hs choice labels ∩ antiCells n).card =
      (labels.filter fun i => choice i = false).card := by
  classical
  have hinj : Function.Injective (fun i => packedRectangleCorner hs choice (i,0)) := by
    intro i j h
    exact congrArg Prod.fst (packedRectangleCorner_injective hs choice h)
  rw [active_rectangle_main_cells hs hL choice labels, active_rectangle_anti_cells hs hL choice labels,
    Finset.card_image_of_injective _ hinj, Finset.card_image_of_injective _ hinj]
  exact ⟨rfl, rfl⟩

end
end Sude
