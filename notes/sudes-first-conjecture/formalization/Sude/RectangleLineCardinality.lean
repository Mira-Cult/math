import Sude.RectangleLineIncidence

/-! Count the actual packed rectangle corners on any row or column. -/
namespace Sude
noncomputable section

/-- Every row contains at most two corners of the entire packed family. -/
theorem packedRectangle_row_card_le_two {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (r : Fin n) :
    ((Finset.univ : Finset (Fin L × Fin 4)).filter
      (fun x => (packedRectangleCorner hs choice x).1 = r)).card ≤ 2 := by
  classical
  let S : Finset (Fin L × Fin 4) := Finset.univ.filter
    (fun x => (packedRectangleCorner hs choice x).1 = r)
  have hcard : S.card ≤ (Finset.univ : Finset Bool).card := by
    apply Finset.card_le_card_of_injOn (fun x => packedCornerColumnSide x.2)
    · intro x hx
      simp
    · intro x hx y hy hside
      change packedCornerColumnSide x.2 = packedCornerColumnSide y.2 at hside
      have hrow : (packedRectangleCorner hs choice x).1 =
          (packedRectangleCorner hs choice y).1 := by
        have hx' := (Finset.mem_filter.mp hx).2
        have hy' := (Finset.mem_filter.mp hy).2
        exact hx'.trans hy'.symm
      have hj : x.1 = y.1 := packedRectangles_same_row hs choice x.1 y.1 x.2 y.2 hrow
      have hcol : (packedRectangleCorner hs choice x).2 =
          (packedRectangleCorner hs choice y).2 := by
        rw [packedCorner_column_slot, packedCorner_column_slot, hj, hside]
      exact packedRectangleCorner_injective hs choice (Prod.ext hrow hcol)
  simpa [S] using hcard

/-- Every column contains at most two corners of the entire packed family. -/
theorem packedRectangle_column_card_le_two {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (c : Fin n) :
    ((Finset.univ : Finset (Fin L × Fin 4)).filter
      (fun x => (packedRectangleCorner hs choice x).2 = c)).card ≤ 2 := by
  classical
  let S : Finset (Fin L × Fin 4) := Finset.univ.filter
    (fun x => (packedRectangleCorner hs choice x).2 = c)
  have hcard : S.card ≤ (Finset.univ : Finset Bool).card := by
    apply Finset.card_le_card_of_injOn (fun x => packedCornerRowSide x.2)
    · intro x hx
      simp
    · intro x hx y hy hside
      change packedCornerRowSide x.2 = packedCornerRowSide y.2 at hside
      have hcol : (packedRectangleCorner hs choice x).2 =
          (packedRectangleCorner hs choice y).2 := by
        have hx' := (Finset.mem_filter.mp hx).2
        have hy' := (Finset.mem_filter.mp hy).2
        exact hx'.trans hy'.symm
      have hj : x.1 = y.1 := packedRectangles_same_column hs choice x.1 y.1 x.2 y.2 hcol
      have hrow : (packedRectangleCorner hs choice x).1 =
          (packedRectangleCorner hs choice y).1 := by
        rw [packedCorner_row_slot, packedCorner_row_slot, hj, hside]
      exact packedRectangleCorner_injective hs choice (Prod.ext hrow hcol)
  simpa [S] using hcard

end
end Sude
