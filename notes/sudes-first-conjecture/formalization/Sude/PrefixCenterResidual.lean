import Sude.PrefixPhysicalLineSum
import Sude.LineResidualDecomposition
import Sude.LayerTranspose

/-! The actual prefix-pair cells never consume the odd-order center. -/
namespace Sude
noncomputable section

/-- Every rectangle and both packed ordinary networks avoid the center. -/
theorem prefixPhysicalCells_avoid_center {P d layers n L : ℕ}
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows rows)
    (packedCols : LayerPacking.PackedLayers reservedCols cols)
    (hn : 0 < n) (hodd : Odd n) (x : PrefixPhysicalInputs P d layers n) :
    prefixPhysicalCells hrect hs choice rows cols hrows hcols x ≠
      (centerIndex n hn, centerIndex n hn) := by
  rcases x with x | (x | x)
  · change packedRectangleCorner hs choice (Fin.castLE hrect x.1, x.2) ≠ _
    intro heq
    have hm := packedRectangleCorner_mem hs choice (Fin.castLE hrect x.1) x.2
    rw [heq] at hm
    exact RectanglePacking.rectangle_avoids_center hs hn choice (Fin.castLE hrect x.1) hm
  · let idx : Fin rows.length := Fin.cast hrows.symm x.1
    have hm := LayerPacking.sequenceCell_mem rows idx x.2
    have hoff := (packedRows.each_layer (rows.get idx) (List.get_mem _ _)).2.1 _ hm
    change LayerPacking.sequenceCell rows (idx, x.2) ≠ _
    intro heq
    have hc := (centerCell_on_both_diagonals n hn hodd).1
    rw [← heq] at hc
    exact hoff.2.1 hc
  · let idx : Fin cols.length := Fin.cast hcols.symm x.1
    have hm := LayerPacking.sequenceCell_mem cols idx x.2
    have hoff := (packedCols.each_layer (cols.get idx) (List.get_mem _ _)).2.1 _ hm
    have hswap : (LayerPacking.sequenceCell cols (idx, x.2)).swap ∉ mainCells n := by
      intro hz
      exact hoff.2.1 ((LayerPacking.swap_mem_main _).mp hz)
    change (LayerPacking.sequenceCell cols (idx, x.2)).swap ≠ _
    intro heq
    have hc := (centerCell_on_both_diagonals n hn hodd).1
    rw [← heq] at hc
    exact hswap hc

/-- The center remains in the residual part of both actual prefix lines. -/
theorem prefixPairCells_center_in_both_residuals {P d layers n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows rows)
    (packedCols : LayerPacking.PackedLayers reservedCols cols)
    (hn : 0 < n) (hodd : Odd n) :
    let cells := prefixPairCells hfit hdiag hexact hrect hs choice rows cols hrows hcols
    (centerIndex n hn, centerIndex n hn) ∈ mainCells n \ Finset.univ.image cells ∧
    (centerIndex n hn, centerIndex n hn) ∈ antiCells n \ Finset.univ.image cells := by
  dsimp only
  apply center_mem_both_line_residuals _ hn hodd
  intro hmem
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hmem
  exact prefixPhysicalCells_avoid_center hrect hs choice rows cols hrows hcols reservedRows reservedCols
    packedRows packedCols hn hodd ((prefixPhysicalInputEquiv hfit hdiag hexact).symm x) hx

end
end Sude
