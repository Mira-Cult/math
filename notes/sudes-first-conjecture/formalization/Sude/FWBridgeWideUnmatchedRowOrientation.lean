import Sude.FWBridgeWideNetworkMatching

/-! The unmatched grouped bridge/wide row orientation vanishes. The gaps
may vary arbitrarily: every unmatched pair has both endpoints in one row. -/
namespace Sude
noncomputable section
open scoped BigOperators
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

/-- A grouped sum supported only on ordinary row-network slots vanishes
outside a set containing all of those slots. -/
theorem fw_unmatched_grouped_sum_zero {n P : ℕ} {α : Type*} [AddCommMonoid α]
    (f : Fin P × Fin (3 * (n + 8)) × Fin 2 → α)
    (T : Finset (Fin P × Fin (3 * (n + 8)) × Fin 2))
    (hrect : ∀ j (rect : Fin (4 * 6)) (p : Fin 2),
      f (j, Fin.castLE (by omega) rect, p) = 0)
    (hperp : ∀ j (edge : Fin 3 × Fin n),
      f (j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge, 1) = 0)
    (hcover : ∀ j (edge : Fin 3 × Fin n),
      (j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge, 0) ∈ T) :
    (∑ i ∈ Finset.univ \ T, f i) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro ⟨j,b,p⟩ hi
  have hnot : (j,b,p) ∉ T := (Finset.mem_sdiff.mp hi).2
  obtain ⟨tag, htag⟩ := (fwControllerStagePairBlock_bijective n).2 (b,p)
  cases tag with
  | inl rp =>
    obtain ⟨rect,pair⟩ := rp
    simp only [fwControllerStagePairBlock] at htag
    cases Prod.mk.inj htag with
    | intro hb hp =>
      subst b
      subst p
      exact hrect j rect pair
  | inr ne =>
    obtain ⟨network,edge⟩ := ne
    simp only [fwControllerStagePairBlock] at htag
    cases Prod.mk.inj htag with
    | intro hb hp =>
      subst b
      subst p
      fin_cases network
      · exact False.elim (hnot (hcover j edge))
      · exact hperp j edge

/-- A bridge rectangle pair stays within one row. -/
theorem fw_bridge_grouped_rectangle_row_orientation_zero {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (j : Fin 5) (rect : Fin (4 * 6)) (p : Fin 2) (r : Fin n) :
    physicalPairLineOrientation (fwBridgePhysicalDoubleCells hrect hs choice rows cols hr hc)
      (fun c => c.1 = r) (j, Fin.castLE (by omega) rect, p) = 0 := by
  classical
  have hcell (side : Bool) : fwBridgePhysicalDoubleCells hrect hs choice rows cols hr hc
      ((j, Fin.castLE (by omega) rect, p), side) =
      packedRectangleCorner hs choice
        (bridgeDiagonalRectangle hrect (finProdFinEquiv (j,rect)), prefixPairCorner p side) := by
    rw [← fw_bridge_reindexed_diagonal_cell hrect hs choice rows cols hr hc j rect p side]
    rw [fwPrefixToControllerPair_diagonal]
    rfl
  unfold physicalPairLineOrientation
  rw [hcell, hcell]
  fin_cases p <;> simp [prefixPairCorner, packedRectangleCorner]

/-- A perpendicular ordinary bridge pair stays within one row. -/
theorem fw_bridge_grouped_perpendicular_row_orientation_zero {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (j : Fin 5) (edge : Fin 3 × Fin n) (r : Fin n) :
    physicalPairLineOrientation (fwBridgePhysicalDoubleCells hrect hs choice rows cols hr hc)
      (fun c => c.1 = r) (j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge, 1) = 0 := by
  classical
  unfold physicalPairLineOrientation
  rw [fw_bridge_double_ordinary_cell, fw_bridge_double_ordinary_cell]
  simp [fwBridgeLayerCells, fwBridgeLayerIndex, LayerPacking.sequenceCell, LayerPacking.layerCell]

/-- A wide rectangle pair stays within one row. -/
theorem fw_wide_grouped_rectangle_row_orientation_zero {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (rect : Fin (4 * 6)) (p : Fin 2) (r : Fin n) :
    physicalPairLineOrientation (fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc)
      (fun c => c.1 = r) (j, Fin.castLE (by omega) rect, p) = 0 := by
  classical
  have hcell (side : Bool) : fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc
      ((j, Fin.castLE (by omega) rect, p), side) =
      packedRectangleCorner hs choice
        (fwWideRectangle hwide (finProdFinEquiv (j,rect)), prefixPairCorner p side) := by
    rw [← fw_wide_reindexed_diagonal_cell hwide hs choice rows cols hr hc j rect p side]
    rw [fwPrefixToControllerPair_diagonal]
    rfl
  unfold physicalPairLineOrientation
  rw [hcell, hcell]
  fin_cases p <;> simp [prefixPairCorner, packedRectangleCorner]

/-- A perpendicular ordinary wide pair stays within one row. -/
theorem fw_wide_grouped_perpendicular_row_orientation_zero {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (edge : Fin 3 × Fin n) (r : Fin n) :
    physicalPairLineOrientation (fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc)
      (fun c => c.1 = r) (j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge, 1) = 0 := by
  classical
  unfold physicalPairLineOrientation
  rw [fw_wide_double_ordinary_cell, fw_wide_double_ordinary_cell]
  simp [fwWidePhysicalCells, fwWideEdgeRole, fwWideOrdinaryCells, fwWideLayerIndex,
    LayerPacking.sequenceCell, LayerPacking.layerCell]

/-- Every unmatched bridge orientation on a row vanishes pointwise, even
when the weight is a different actual gap at every pair. -/
theorem fw_bridge_unmatched_row_orientation_zero {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr wr gr : List (LayerPacking.Layer n)) (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (weight : Fin 5 × Fin (3 * (n + 8)) × Fin 2 → ℝ) (r : Fin n) :
    (∑ i ∈ Finset.univ \ (fwBridgeJointPairImage br sr wr gr hbr).image
        (fwBridgeJointToGrouped br sr wr gr hbr 0),
      weight i * physicalPairLineOrientation (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
        (fun c => c.1 = r) i) = 0 := by
  classical
  apply fw_unmatched_grouped_sum_zero
  · intro j rect p
    rw [fw_bridge_grouped_rectangle_row_orientation_zero]
    simp
  · intro j edge
    rw [fw_bridge_grouped_perpendicular_row_orientation_zero]
    simp
  · intro j edge
    apply Finset.mem_image.mpr
    refine ⟨(fwBridgeJointLayerIndex br sr wr gr hbr j edge.1, edge.2), ?_, ?_⟩
    · unfold fwBridgeJointPairImage
      exact Finset.mem_image.mpr ⟨((j,edge.1),edge.2), Finset.mem_univ _, rfl⟩
    · exact fw_bridge_joint_to_grouped br sr wr gr hbr 0 j edge.1 edge.2

/-- Every unmatched wide orientation on a row vanishes pointwise, with
arbitrary pair-dependent weights. -/
theorem fw_wide_unmatched_row_orientation_zero {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br sr wr gr wc : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hJ : 0 < 3 * (n / 450))
    (weight : Fin (3 * (n / 450)) × Fin (3 * (n + 8)) × Fin 2 → ℝ) (r : Fin n) :
    (∑ i ∈ Finset.univ \ (fwWideJointPairImage br sr wr gr hwr).image
        (fwWideJointToGrouped hJ br sr wr gr hwr 0),
      weight i * physicalPairLineOrientation (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
        (fun c => c.1 = r) i) = 0 := by
  classical
  apply fw_unmatched_grouped_sum_zero
  · intro j rect p
    rw [fw_wide_grouped_rectangle_row_orientation_zero]
    simp
  · intro j edge
    rw [fw_wide_grouped_perpendicular_row_orientation_zero]
    simp
  · intro j edge
    apply Finset.mem_image.mpr
    refine ⟨(fwWideJointLayerIndex br sr wr gr hwr j edge.1, edge.2), ?_, ?_⟩
    · unfold fwWideJointPairImage
      exact Finset.mem_image.mpr ⟨((j,edge.1),edge.2), Finset.mem_univ _, rfl⟩
    · exact fw_wide_joint_to_grouped hJ br sr wr gr hwr 0 j edge.1 edge.2

end
end Sude
