import Sude.FWGrowthOrdinaryRowColumnMass

/-! Each complete growth stage has zero net row and column orientation.
This is geometric algebra; it does not bound entries or diagonals. -/
namespace Sude
noncomputable section
set_option maxRecDepth 8192

/-- A growth rectangle pair has both endpoints in the same row. -/
theorem fw_growth_rectangle_pair_row_orientation_zero {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P*3) (hc : cols.length = P*3)
    (j : Fin P) (rect : Fin (4*6)) (pair : Fin 2) (r : Fin n) :
    physicalPairLineOrientation
      (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        offset hoff hs choice rows cols hr hc) (fun z => z.1 = r)
      (j, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (rect,pair)) = 0 := by
  classical
  unfold physicalPairLineOrientation
  rw [fw_growth_offset_rectangle_cell, fw_growth_offset_rectangle_cell]
  fin_cases pair <;> simp [prefixPairCorner, packedRectangleCorner]

/-- The two growth rectangle pairs have opposite column orientation. -/
theorem fw_growth_rectangle_pairs_column_orientation_zero {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P*3) (hc : cols.length = P*3)
    (j : Fin P) (rect : Fin (4*6)) (c : Fin n) :
    (∑ pair : Fin 2, physicalPairLineOrientation
      (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        offset hoff hs choice rows cols hr hc) (fun z => z.2 = c)
      (j, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (rect,pair))) = 0 := by
  classical
  rw [Fin.sum_univ_two]
  unfold physicalPairLineOrientation
  rw [fw_growth_offset_rectangle_cell, fw_growth_offset_rectangle_cell,
    fw_growth_offset_rectangle_cell, fw_growth_offset_rectangle_cell]
  simp [prefixPairCorner, packedRectangleCorner]

/-- Each complete growth stage has zero net orientation on every row. -/
theorem fw_growth_stage_row_orientation_zero {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P*3) (hc : cols.length = P*3) (j : Fin P) (r : Fin n) :
    (∑ q : Fin (6*(n+8)), physicalPairLineOrientation
      (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        offset hoff hs choice rows cols hr hc) (fun z => z.1 = r) (j,q)) = 0 := by
  classical
  let hfit : (4*6)*2 + 2*(3*n) ≤ 6*(n+8) := by omega
  let hdiag : (4*6)*2 ≤ 6*(n+8) := by omega
  let hexact : (4*6)*2 + 2*(3*n) = 6*(n+8) := by omega
  let e := Equiv.ofBijective (prefixStagePairSlot hfit hdiag)
    (prefixStagePairSlot_bijective hfit hdiag hexact)
  let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) hfit hdiag hexact offset hoff hs choice rows cols hr hc
  let orient := physicalPairLineOrientation cells (fun z => z.1 = r)
  change (∑ q, orient (j,q)) = 0
  rw [← e.sum_comp (fun q => orient (j,q))]
  simp only [e, Equiv.ofBijective_apply, prefixStagePairSlot, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  have hrect : (∑ p : Fin (4*6) × Fin 2, orient (j,prefixDiagonalPairIndex hdiag p)) = 0 := by
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero; intro rect _
    apply Finset.sum_eq_zero; intro pair _
    exact fw_growth_rectangle_pair_row_orientation_zero offset hoff hs choice rows cols hr hc j rect pair r
  have hrow : (∑ k : Fin 3, ∑ t : Fin n, orient (j,prefixOrdinaryPairIndex hfit (0,k,t))) = 0 := by
    apply Finset.sum_eq_zero; intro k _
    let layer := prefixStageLayer rows hr j k
    have he := Equiv.sum_comp layer.1 (fun v : Fin n => if v = r then (1 : ℝ) else 0)
    simp only [orient, cells, physicalPairLineOrientation, fw_growth_ordinary_row_cell,
      LayerPacking.layerCell, Finset.sum_sub_distrib]
    simpa [layer] using sub_eq_zero.mpr he
  have hcol : (∑ k : Fin 3, ∑ t : Fin n, orient (j,prefixOrdinaryPairIndex hfit (1,k,t))) = 0 := by
    apply Finset.sum_eq_zero; intro k _
    apply Finset.sum_eq_zero; intro t _
    simp [orient, cells, physicalPairLineOrientation, fw_growth_ordinary_column_cell, LayerPacking.layerCell]
  have hrect' : (∑ rect : Fin (4*6),
      (orient (j,prefixDiagonalPairIndex hdiag (rect,0)) +
       orient (j,prefixDiagonalPairIndex hdiag (rect,1)))) = 0 := by
    simpa only [Fintype.sum_prod_type, Fin.sum_univ_two] using hrect
  rw [hrect', hrow, hcol]
  norm_num

/-- Each complete growth stage has zero net orientation on every column. -/
theorem fw_growth_stage_column_orientation_zero {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P*3) (hc : cols.length = P*3) (j : Fin P) (c : Fin n) :
    (∑ q : Fin (6*(n+8)), physicalPairLineOrientation
      (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        offset hoff hs choice rows cols hr hc) (fun z => z.2 = c) (j,q)) = 0 := by
  classical
  let hfit : (4*6)*2 + 2*(3*n) ≤ 6*(n+8) := by omega
  let hdiag : (4*6)*2 ≤ 6*(n+8) := by omega
  let hexact : (4*6)*2 + 2*(3*n) = 6*(n+8) := by omega
  let e := Equiv.ofBijective (prefixStagePairSlot hfit hdiag)
    (prefixStagePairSlot_bijective hfit hdiag hexact)
  let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) hfit hdiag hexact offset hoff hs choice rows cols hr hc
  let orient := physicalPairLineOrientation cells (fun z => z.2 = c)
  change (∑ q, orient (j,q)) = 0
  rw [← e.sum_comp (fun q => orient (j,q))]
  simp only [e, Equiv.ofBijective_apply, prefixStagePairSlot, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  have hrect : (∑ p : Fin (4*6) × Fin 2, orient (j,prefixDiagonalPairIndex hdiag p)) = 0 := by
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero; intro rect _
    exact fw_growth_rectangle_pairs_column_orientation_zero offset hoff hs choice rows cols hr hc j rect c
  have hrow : (∑ k : Fin 3, ∑ t : Fin n, orient (j,prefixOrdinaryPairIndex hfit (0,k,t))) = 0 := by
    apply Finset.sum_eq_zero; intro k _
    apply Finset.sum_eq_zero; intro t _
    simp [orient, cells, physicalPairLineOrientation, fw_growth_ordinary_row_cell, LayerPacking.layerCell]
  have hcol : (∑ k : Fin 3, ∑ t : Fin n, orient (j,prefixOrdinaryPairIndex hfit (1,k,t))) = 0 := by
    apply Finset.sum_eq_zero; intro k _
    let layer := prefixStageLayer cols hc j k
    have he := Equiv.sum_comp layer.1 (fun v : Fin n => if v = c then (1 : ℝ) else 0)
    simp only [orient, cells, physicalPairLineOrientation, fw_growth_ordinary_column_cell,
      LayerPacking.layerCell, Finset.sum_sub_distrib]
    simpa [layer] using sub_eq_zero.mpr he
  have hrect' : (∑ rect : Fin (4*6),
      (orient (j,prefixDiagonalPairIndex hdiag (rect,0)) +
       orient (j,prefixDiagonalPairIndex hdiag (rect,1)))) = 0 := by
    simpa only [Fintype.sum_prod_type, Fin.sum_univ_two] using hrect
  rw [hrect', hrow, hcol]
  norm_num

end
end Sude
