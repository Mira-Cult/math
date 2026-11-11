import Sude.CYFullKeepoutGeometry
import Sude.FWFullReservationLineIncidence

namespace Sude
noncomputable section

/-- Ordinary off-diagonal layers add the same count to every line after
including the full rectangle keepout and both diagonals. -/
theorem cy_rectangle_diagonal_layers_load {L n : ℕ}
    (hs : 2*L+1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols) :
    let rect := packedRectangleSupport hs choice
    let diag := mainCells n ∪ antiCells n
    let full := rect ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols)
    let final := full ∪ unreservedDiagonalCells full
    (∀ i, (LayerPacking.rowUsed final i).card =
      (LayerPacking.rowUsed (rect ∪ diag) i).card + 2 * (rows.length + cols.length)) ∧
    (∀ i, (LayerPacking.colUsed final i).card =
      (LayerPacking.colUsed (rect ∪ diag) i).card + 2 * (rows.length + cols.length)) := by
  classical
  dsimp only
  let rect := packedRectangleSupport hs choice
  let diag := mainCells n ∪ antiCells n
  let R := LayerPacking.layersSupport rows
  let C := LayerPacking.transposeCells (LayerPacking.layersSupport cols)
  let full := rect ∪ R ∪ C
  let final := full ∪ unreservedDiagonalCells full
  have hfinal : final = (rect ∪ diag) ∪ R ∪ C := by
    ext z
    dsimp [final, full, unreservedDiagonalCells, rect, diag, R, C]
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have hrdis : Disjoint (rect ∪ diag) R := by
    apply Finset.disjoint_left.mpr
    intro z hz hzR
    rcases Finset.mem_union.mp hz with hzrect | hzdiag
    · exact Finset.disjoint_left.mp hrows.reserved_disjoint hzrect hzR
    · have ho := hrows.support_off_diagonals z hzR
      rcases Finset.mem_union.mp hzdiag with hm | ha
      · exact ho.1 hm
      · exact ho.2 ha
  have hcdis : Disjoint ((rect ∪ diag) ∪ R) C := by
    apply Finset.disjoint_left.mpr
    intro z hz hzC
    have ho := hcols.transposed_support_safe z hzC
    rcases Finset.mem_union.mp hz with hz | hzR
    · rcases Finset.mem_union.mp hz with hzrect | hzdiag
      · exact ho.1 (Finset.mem_union_left _ hzrect)
      · rcases Finset.mem_union.mp hzdiag with hm | ha
        · exact ho.2.1 hm
        · exact ho.2.2 ha
    · exact ho.1 (Finset.mem_union_right _ hzR)
  have rowDis {A B : Finset (Cell n)} (hab : Disjoint A B) (i : Fin n) :
      Disjoint (LayerPacking.rowUsed A i) (LayerPacking.rowUsed B i) := by
    apply Finset.disjoint_left.mpr
    intro j ha hb
    exact Finset.disjoint_left.mp hab (by simpa [LayerPacking.rowUsed] using ha)
      (by simpa [LayerPacking.rowUsed] using hb)
  have colDis {A B : Finset (Cell n)} (hab : Disjoint A B) (i : Fin n) :
      Disjoint (LayerPacking.colUsed A i) (LayerPacking.colUsed B i) := by
    apply Finset.disjoint_left.mpr
    intro j ha hb
    exact Finset.disjoint_left.mp hab (by simpa [LayerPacking.colUsed] using ha)
      (by simpa [LayerPacking.colUsed] using hb)
  constructor
  · intro i
    change (LayerPacking.rowUsed final i).card = (LayerPacking.rowUsed (rect ∪ diag) i).card + _
    rw [hfinal, LayerPacking.rowUsed_union, Finset.card_union_of_disjoint (rowDis hcdis i),
      LayerPacking.rowUsed_union, Finset.card_union_of_disjoint (rowDis hrdis i)]
    have hrowR : (LayerPacking.rowUsed R i).card = 2*rows.length := by
      rw [LayerPacking.rowUsed_card_eq]
      exact hrows.row_balance i
    have hrowC : (LayerPacking.rowUsed C i).card = 2*cols.length := by
      rw [LayerPacking.rowUsed_transpose, LayerPacking.colUsed_card_eq]
      exact hcols.column_balance i
    rw [hrowR, hrowC]
    omega
  · intro i
    change (LayerPacking.colUsed final i).card = (LayerPacking.colUsed (rect ∪ diag) i).card + _
    rw [hfinal, LayerPacking.colUsed_union, Finset.card_union_of_disjoint (colDis hcdis i),
      LayerPacking.colUsed_union, Finset.card_union_of_disjoint (colDis hrdis i)]
    have hcolR : (LayerPacking.colUsed R i).card = 2*rows.length := by
      rw [LayerPacking.colUsed_card_eq]
      exact hrows.column_balance i
    have hcolC : (LayerPacking.colUsed C i).card = 2*cols.length := by
      rw [LayerPacking.colUsed_transpose, LayerPacking.rowUsed_card_eq]
      exact hcols.row_balance i
    rw [hcolR, hcolC]
    omega
end
end Sude
