import Sude.FWBridgeWideUnmatchedRowOrientation

/-! Unmatched grouped column orientations cancel under the explicit condition
that the two pairs in each rectangle have the same weight. -/
namespace Sude
noncomputable section
open scoped BigOperators
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

/-- A grouped sum with cancelling rectangle pairs and zero perpendicular
ordinary terms vanishes outside the exact selected column-network sum. -/
theorem fw_unmatched_grouped_column_sum_zero {n P : ℕ}
    (f : Fin P × Fin (3 * (n + 8)) × Fin 2 → ℝ)
    (T : Finset (Fin P × Fin (3 * (n + 8)) × Fin 2))
    (hrect : ∀ j (rect : Fin (4 * 6)),
      (∑ p : Fin 2, f (j, Fin.castLE (by omega) rect, p)) = 0)
    (hperp : ∀ j (edge : Fin 3 × Fin n),
      f (j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge, 0) = 0)
    (hnet : (∑ i ∈ T, f i) = ∑ j : Fin P, ∑ edge : Fin 3 × Fin n,
      f (j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge, 1)) :
    (∑ i ∈ Finset.univ \ T, f i) = 0 := by
  classical
  simp only [Fin.sum_univ_two] at hrect
  let E := Equiv.ofBijective (fwControllerStagePairBlock n) (fwControllerStagePairBlock_bijective n)
  have hstage (j : Fin P) :
      (∑ q : Fin (3 * (n + 8)) × Fin 2, f (j,q.1,q.2)) =
        ∑ edge : Fin 3 × Fin n,
          f (j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge, 1) := by
    calc
      _ = ∑ tag : PrefixStagePair 6 3 n, f (j,(E tag).1,(E tag).2) :=
        (E.sum_comp (fun q => f (j,q.1,q.2))).symm
      _ = _ := by
        simp only [E, Equiv.ofBijective_apply, fwControllerStagePairBlock,
          Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two]
        simp only [hrect, hperp, Finset.sum_const_zero, zero_add]
  have htotal : (∑ i : Fin P × Fin (3 * (n + 8)) × Fin 2, f i) = ∑ i ∈ T, f i := by
    rw [hnet, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun j _ => hstage j)
  have hsplit := Finset.sum_sdiff (Finset.subset_univ T) (f := f)
  rw [← htotal] at hsplit
  linarith

/-- The two bridge rectangle pairs have opposite column orientation. -/
theorem fw_bridge_grouped_rectangle_column_orientations_cancel {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (j : Fin 5) (rect : Fin (4 * 6)) (c : Fin n) :
    (∑ p : Fin 2, physicalPairLineOrientation (fwBridgePhysicalDoubleCells hrect hs choice rows cols hr hc)
      (fun x => x.2 = c) (j, Fin.castLE (by omega) rect, p)) = 0 := by
  classical
  have hcell (p : Fin 2) (side : Bool) : fwBridgePhysicalDoubleCells hrect hs choice rows cols hr hc
      ((j, Fin.castLE (by omega) rect, p), side) =
      packedRectangleCorner hs choice
        (bridgeDiagonalRectangle hrect (finProdFinEquiv (j,rect)), prefixPairCorner p side) := by
    rw [← fw_bridge_reindexed_diagonal_cell hrect hs choice rows cols hr hc j rect p side]
    rw [fwPrefixToControllerPair_diagonal]
    rfl
  rw [Fin.sum_univ_two]
  unfold physicalPairLineOrientation
  rw [hcell, hcell, hcell, hcell]
  simp [prefixPairCorner, packedRectangleCorner]

/-- The ordinary row-network pair stays within a physical column. -/
theorem fw_bridge_grouped_perpendicular_column_orientation_zero {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (j : Fin 5) (edge : Fin 3 × Fin n) (c : Fin n) :
    physicalPairLineOrientation (fwBridgePhysicalDoubleCells hrect hs choice rows cols hr hc)
      (fun x => x.2 = c) (j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge, 0) = 0 := by
  classical
  unfold physicalPairLineOrientation
  rw [fw_bridge_double_ordinary_cell, fw_bridge_double_ordinary_cell]
  simp [fwBridgeLayerCells, fwBridgeLayerIndex, LayerPacking.sequenceCell, LayerPacking.layerCell]

/-- The two wide rectangle pairs have opposite column orientation. -/
theorem fw_wide_grouped_rectangle_column_orientations_cancel {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (rect : Fin (4 * 6)) (c : Fin n) :
    (∑ p : Fin 2, physicalPairLineOrientation (fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc)
      (fun x => x.2 = c) (j, Fin.castLE (by omega) rect, p)) = 0 := by
  classical
  have hcell (p : Fin 2) (side : Bool) : fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc
      ((j, Fin.castLE (by omega) rect, p), side) =
      packedRectangleCorner hs choice
        (fwWideRectangle hwide (finProdFinEquiv (j,rect)), prefixPairCorner p side) := by
    rw [← fw_wide_reindexed_diagonal_cell hwide hs choice rows cols hr hc j rect p side]
    rw [fwPrefixToControllerPair_diagonal]
    rfl
  rw [Fin.sum_univ_two]
  unfold physicalPairLineOrientation
  rw [hcell, hcell, hcell, hcell]
  simp [prefixPairCorner, packedRectangleCorner]

/-- The ordinary wide row-network pair stays within one column. -/
theorem fw_wide_grouped_perpendicular_column_orientation_zero {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (edge : Fin 3 × Fin n) (c : Fin n) :
    physicalPairLineOrientation (fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc)
      (fun x => x.2 = c) (j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge, 0) = 0 := by
  classical
  unfold physicalPairLineOrientation
  rw [fw_wide_double_ordinary_cell, fw_wide_double_ordinary_cell]
  simp [fwWidePhysicalCells, fwWideEdgeRole, fwWideOrdinaryCells, fwWideLayerIndex,
    LayerPacking.sequenceCell, LayerPacking.layerCell]

/-- The unmatched bridge column orientations cancel when each rectangle's
two pair weights agree. No equality is required between different blocks. -/
theorem fw_bridge_unmatched_column_orientation_zero {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sc wc gc : List (LayerPacking.Layer n)) (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (weight : Fin 5 × Fin (3 * (n + 8)) × Fin 2 → ℝ)
    (heq : ∀ j (rect : Fin (4 * 6)),
      weight (j, Fin.castLE (by omega) rect, 0) = weight (j, Fin.castLE (by omega) rect, 1)) (c : Fin n) :
    (∑ i ∈ Finset.univ \ (fwBridgeJointPairImage bc sc wc gc hbc).image
        (fwBridgeJointToGrouped bc sc wc gc hbc 1),
      weight i * physicalPairLineOrientation (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
        (fun x => x.2 = c) i) = 0 := by
  classical
  apply fw_unmatched_grouped_column_sum_zero
  · intro j rect
    rw [Fin.sum_univ_two, heq j rect, ← mul_add]
    have h := fw_bridge_grouped_rectangle_column_orientations_cancel hrect hs choice br bc hbr hbc j rect c
    rw [Fin.sum_univ_two] at h
    rw [h, mul_zero]
  · intro j edge
    rw [fw_bridge_grouped_perpendicular_column_orientation_zero]
    simp
  · rw [Finset.sum_image (fw_bridge_joint_grouped_injective_on_image bc sc wc gc hbc 1)]
    unfold fwBridgeJointPairImage
    rw [Finset.sum_image (fwBridgeJointPairIndex_injective bc sc wc gc hbc).injOn]
    simp only [Fintype.sum_prod_type, fw_bridge_joint_to_grouped]

/-- The unmatched wide column orientations cancel when each rectangle's
pair weights agree; different rectangle blocks may have different weights. -/
theorem fw_wide_unmatched_column_orientation_zero {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (wr bc sc wc gc : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hJ : 0 < 3 * (n / 450))
    (weight : Fin (3 * (n / 450)) × Fin (3 * (n + 8)) × Fin 2 → ℝ)
    (heq : ∀ j (rect : Fin (4 * 6)),
      weight (j, Fin.castLE (by omega) rect, 0) = weight (j, Fin.castLE (by omega) rect, 1)) (c : Fin n) :
    (∑ i ∈ Finset.univ \ (fwWideJointPairImage bc sc wc gc hwc).image
        (fwWideJointToGrouped hJ bc sc wc gc hwc 1),
      weight i * physicalPairLineOrientation (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
        (fun x => x.2 = c) i) = 0 := by
  classical
  apply fw_unmatched_grouped_column_sum_zero
  · intro j rect
    rw [Fin.sum_univ_two, heq j rect, ← mul_add]
    have h := fw_wide_grouped_rectangle_column_orientations_cancel hwide hs choice wr wc hwr hwc j rect c
    rw [Fin.sum_univ_two] at h
    rw [h, mul_zero]
  · intro j edge
    rw [fw_wide_grouped_perpendicular_column_orientation_zero]
    simp
  · rw [Finset.sum_image (fw_wide_joint_grouped_injective_on_image hJ bc sc wc gc hwc 1)]
    unfold fwWideJointPairImage
    rw [Finset.sum_image (fwWideJointPairIndex_injective bc sc wc gc hwc).injOn]
    simp only [Fintype.sum_prod_type, fw_wide_joint_to_grouped]

end
end Sude
