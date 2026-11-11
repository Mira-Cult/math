import Sude.FWFullReservationLineIncidence
import Sude.CentralConstruct

/-! Same-support FW geometry for the post-diagonal completion interface.
This supplies neither stock nor primality of the resulting diagonal sums. -/
namespace Sude
noncomputable section

/-- The first-band arithmetic supplies the RF3 load gate for `b = 0`. -/
theorem fw_first_band_post_diagonal_load {n P : ℕ}
    (hn : 19485 ≤ n) (_hnhi : n ≤ 35733) (hP : P ≤ 238) :
    4 * (12 * (5 + 16 + 3 * (n / 450) + P) + 4) ≤ n := by
  have := Nat.mul_div_le n 450
  omega

/-- The full FW keepout enlarged by its previously unreserved diagonal cells
contains both diagonals and has row/column loads between `12*S` and `12*S+4`.
All geometry uses the same rectangle choice and packed layer lists. -/
theorem fw_post_diagonal_completion_geometry {n P : ℕ}
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (hbc : bc.length = 5 * 3) (hsc : sc.length = 16 * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice)
      (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc)) :
    let S := 5 + 16 + 3 * (n / 450) + P
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    let final := full ∪ unreservedDiagonalCells full
    mainCells n ⊆ final ∧ antiCells n ⊆ final ∧
    (∀ i, 12 * S ≤ (LayerPacking.rowUsed final i).card ∧
      (LayerPacking.rowUsed final i).card ≤ 12 * S + 4) ∧
    (∀ i, 12 * S ≤ (LayerPacking.colUsed final i).card ∧
      (LayerPacking.colUsed final i).card ≤ 12 * S + 4) := by
  classical
  dsimp only
  let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
  let final := full ∪ unreservedDiagonalCells full
  have hocc := fw_full_reservation_line_incidence hs choice br sr wr gr bc sc wc gc
    hbr hsr hwr hgr hbc hsc hwc hgc hrows hcols
  dsimp only at hocc
  have hdiags := postDiagonal_contains_both full
  refine ⟨hdiags.1, hdiags.2, ?_, ?_⟩
  · intro i
    change 12 * (5 + 16 + 3 * (n / 450) + P) ≤ (LayerPacking.rowUsed final i).card ∧
      (LayerPacking.rowUsed final i).card ≤ 12 * (5 + 16 + 3 * (n / 450) + P) + 4
    have hsub : LayerPacking.rowUsed full i ⊆ LayerPacking.rowUsed final i := by
      intro j hj
      have hm : (i,j) ∈ full := by simpa [LayerPacking.rowUsed] using hj
      have hm' : (i,j) ∈ final := Finset.mem_union_left _ hm
      simpa [LayerPacking.rowUsed] using hm'
    have hlo := Finset.card_le_card hsub
    have hhi : (LayerPacking.rowUsed final i).card ≤
        (LayerPacking.rowUsed full i).card + (LayerPacking.rowUsed (unreservedDiagonalCells full) i).card := by
      dsimp [final]
      rw [LayerPacking.rowUsed_union]
      exact Finset.card_union_le _ _
    have hd : (LayerPacking.rowUsed (unreservedDiagonalCells full) i).card ≤ 2 := by
      rw [← factor_row_cells_card]
      exact row_unreserved_diagonal_card_le_two full i
    have hi : (LayerPacking.rowUsed full i).card = 12 * (5 + 16 + 3 * (n / 450) + P) ∨
        (LayerPacking.rowUsed full i).card = 12 * (5 + 16 + 3 * (n / 450) + P) + 2 := hocc.1 i
    rcases hi with he | he <;> omega
  · intro i
    change 12 * (5 + 16 + 3 * (n / 450) + P) ≤ (LayerPacking.colUsed final i).card ∧
      (LayerPacking.colUsed final i).card ≤ 12 * (5 + 16 + 3 * (n / 450) + P) + 4
    have hsub : LayerPacking.colUsed full i ⊆ LayerPacking.colUsed final i := by
      intro j hj
      have hm : (j,i) ∈ full := by simpa [LayerPacking.colUsed] using hj
      have hm' : (j,i) ∈ final := Finset.mem_union_left _ hm
      simpa [LayerPacking.colUsed] using hm'
    have hlo := Finset.card_le_card hsub
    have hhi : (LayerPacking.colUsed final i).card ≤
        (LayerPacking.colUsed full i).card + (LayerPacking.colUsed (unreservedDiagonalCells full) i).card := by
      dsimp [final]
      rw [LayerPacking.colUsed_union]
      exact Finset.card_union_le _ _
    have hd : (LayerPacking.colUsed (unreservedDiagonalCells full) i).card ≤ 2 := by
      rw [← factor_column_cells_card]
      exact column_unreserved_diagonal_card_le_two full i
    have hi : (LayerPacking.colUsed full i).card = 12 * (5 + 16 + 3 * (n / 450) + P) ∨
        (LayerPacking.colUsed full i).card = 12 * (5 + 16 + 3 * (n / 450) + P) + 2 := hocc.2.1 i
    rcases hi with he | he <;> omega

/-- The full FW reservation avoids the square center. -/
theorem fw_full_keepout_avoids_center {L n : ℕ} (hs : 2 * L + 1 ≤ n) (hn : 0 < n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols) :
    centralCell n hn ∉ packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
  classical
  intro h
  rcases Finset.mem_union.mp h with h | h
  · rcases Finset.mem_union.mp h with h | h
    · obtain ⟨⟨i, side⟩, _, heq⟩ := Finset.mem_image.mp h
      have hm := packedRectangleCorner_mem hs choice i side
      rw [heq] at hm
      exact RectanglePacking.rectangle_avoids_center hs hn choice i hm
    · exact (hrows.support_off_diagonals _ h).1 ((mem_mainCells _).2 rfl)
  · exact (hcols.transposed_support_safe _ h).2.1 ((mem_mainCells _).2 rfl)

end
end Sude
