import Sude.FWGrowthDiagonalPhysical
import Sude.FWSeedLineIncidence

/-! The ordinary growth pairs have exactly twelve row and column incidences
per stage. Both endpoints are counted even when a layer edge is a loop. -/
namespace Sude
noncomputable section

/-- Actual ordinary row slot for the offset growth allocation. -/
theorem fw_growth_ordinary_row_cell {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = P * 3)
    (hsc : sc.length = P * 3) (j : Fin P) (k : Fin 3) (edge : Fin n) (side : Bool) :
    btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega) offset hoff hs choice sr sc hsr hsc
      ((j, prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (0, k, edge)), side) =
    LayerPacking.layerCell (prefixStageLayer sr hsr j k).1
      (prefixStageLayer sr hsr j k).2 (edge, side) := by
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let hexact : (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega
  let e := prefixPhysicalInputEquiv (P := P) hfit hdiag hexact
  have he : e.symm ((j, prefixOrdinaryPairIndex hfit (0, k, edge)), side) =
      Sum.inr (Sum.inl (finProdFinEquiv (j, k), (edge, side))) := by
    apply e.symm_apply_eq.mpr
    simpa [e, prefixPhysicalInputEquiv, prefixPhysicalInput] using (prefixStageLayer_networkInput hfit rfl 0 j k edge side).symm
  change btGrowingOffsetCells offset hoff hs choice sr sc hsr hsc
    (e.symm ((j, prefixOrdinaryPairIndex hfit (0, k, edge)), side)) = _
  rw [he]
  exact prefixStageLayer_sequenceCell sr hsr j k edge side

/-- Actual ordinary column slot, in original (untransposed) square coordinates. -/
theorem fw_growth_ordinary_column_cell {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = P * 3)
    (hsc : sc.length = P * 3) (j : Fin P) (k : Fin 3) (edge : Fin n) (side : Bool) :
    btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega) offset hoff hs choice sr sc hsr hsc
      ((j, prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (1, k, edge)), side) =
    (LayerPacking.layerCell (prefixStageLayer sc hsc j k).1
      (prefixStageLayer sc hsc j k).2 (edge, side)).swap := by
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let hexact : (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega
  let e := prefixPhysicalInputEquiv (P := P) hfit hdiag hexact
  have he : e.symm ((j, prefixOrdinaryPairIndex hfit (1, k, edge)), side) =
      Sum.inr (Sum.inr (finProdFinEquiv (j, k), (edge, side))) := by
    apply e.symm_apply_eq.mpr
    simpa [e, prefixPhysicalInputEquiv, prefixPhysicalInput] using (prefixStageLayer_networkInput hfit rfl 1 j k edge side).symm
  change btGrowingOffsetCells offset hoff hs choice sr sc hsr hsc
    (e.symm ((j, prefixOrdinaryPairIndex hfit (1, k, edge)), side)) = _
  rw [he]
  exact congrArg Prod.swap (prefixStageLayer_sequenceCell sc hsc j k edge side)


/-- The six ordinary layers contribute exactly twelve endpoints to every row. -/
theorem fw_growth_ordinary_row_mass {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = P*3) (hsc : sc.length = P*3)
    (j : Fin P) (r : Fin n) :
    (∑ i ∈ fwGrowthOrdinarySlots n,
      physicalPairLineWeight
        (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
          offset hoff hs choice sr sc hsr hsc)
        (fun z => z.1 = r) (j,i)) = 12 := by
  classical
  have h0 (k : Fin 3) (edge : Fin n) :
      physicalPairLineWeight (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega) offset hoff hs choice sr sc hsr hsc) (fun z => z.1 = r)
        (j, prefixOrdinaryPairIndex (show (4*6)*2+2*(3*n) ≤ 6*(n+8) by omega) (0,k,edge)) =
      LayerPacking.layerRowWeight (prefixStageLayer sr hsr j k).1
        (prefixStageLayer sr hsr j k).2 r edge := by
    simp [physicalPairLineWeight, fw_growth_ordinary_row_cell, LayerPacking.layerRowWeight]
  have h1 (k : Fin 3) (edge : Fin n) :
      physicalPairLineWeight (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega) offset hoff hs choice sr sc hsr hsc) (fun z => z.1 = r)
        (j, prefixOrdinaryPairIndex (show (4*6)*2+2*(3*n) ≤ 6*(n+8) by omega) (1,k,edge)) =
      LayerPacking.layerColumnWeight (prefixStageLayer sc hsc j k).1
        (prefixStageLayer sc hsc j k).2 r edge := by
    simp [physicalPairLineWeight, fw_growth_ordinary_column_cell, LayerPacking.layerColumnWeight]
  unfold fwGrowthOrdinarySlots
  rw [Finset.sum_image]
  · simp only [Fintype.sum_prod_type, Fin.sum_univ_two, h0, h1,
      layer_row_weight_sum, layer_column_weight_sum]
    norm_num
  · exact (prefixOrdinaryPairIndex_injective (d := 6) (r := 3) (n := n)
      (Q := 6*(n+8)) (by omega)).injOn

/-- The six ordinary layers contribute exactly twelve endpoints to every column. -/
theorem fw_growth_ordinary_column_mass {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = P*3) (hsc : sc.length = P*3)
    (j : Fin P) (c : Fin n) :
    (∑ i ∈ fwGrowthOrdinarySlots n,
      physicalPairLineWeight
        (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
          offset hoff hs choice sr sc hsr hsc)
        (fun z => z.2 = c) (j,i)) = 12 := by
  classical
  have h0 (k : Fin 3) (edge : Fin n) :
      physicalPairLineWeight (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega) offset hoff hs choice sr sc hsr hsc) (fun z => z.2 = c)
        (j, prefixOrdinaryPairIndex (show (4*6)*2+2*(3*n) ≤ 6*(n+8) by omega) (0,k,edge)) =
      LayerPacking.layerColumnWeight (prefixStageLayer sr hsr j k).1
        (prefixStageLayer sr hsr j k).2 c edge := by
    simp [physicalPairLineWeight, fw_growth_ordinary_row_cell, LayerPacking.layerColumnWeight]
  have h1 (k : Fin 3) (edge : Fin n) :
      physicalPairLineWeight (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega) offset hoff hs choice sr sc hsr hsc) (fun z => z.2 = c)
        (j, prefixOrdinaryPairIndex (show (4*6)*2+2*(3*n) ≤ 6*(n+8) by omega) (1,k,edge)) =
      LayerPacking.layerRowWeight (prefixStageLayer sc hsc j k).1
        (prefixStageLayer sc hsc j k).2 c edge := by
    simp [physicalPairLineWeight, fw_growth_ordinary_column_cell, LayerPacking.layerRowWeight]
  unfold fwGrowthOrdinarySlots
  rw [Finset.sum_image]
  · simp only [Fintype.sum_prod_type, Fin.sum_univ_two, h0, h1,
      layer_row_weight_sum, layer_column_weight_sum]
    norm_num
  · exact (prefixOrdinaryPairIndex_injective (d := 6) (r := 3) (n := n)
      (Q := 6*(n+8)) (by omega)).injOn

end
end Sude
