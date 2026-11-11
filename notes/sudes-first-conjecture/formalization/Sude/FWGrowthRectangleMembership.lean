import Sude.FWGrowthOrdinaryRowColumnMass
import Sude.FWJointPackedOccupancy

/-! Physical growth rectangle labels are active, while the ordinary growth
layers avoid every packed rectangle. This is geometry only. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384

/-- For the actual FW growth offset, all rectangle endpoint slots are active;
all ordinary row and transposed-column endpoints avoid the active support.
The supplied packed prefixes can be the actual bridge/seed/wide layers. -/
theorem fw_growth_rectangle_ordinary_support {n P : ℕ} (hP : P ≤ 238)
    (hoff : 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)+P*(4*6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (preRows preCols gr gc : List (LayerPacking.Layer n))
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (preRows ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (preRows ++ gr))) (preCols ++ gc)) :
    let offset := 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice gr gc hgr hgc
    let active := activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
    (∀ j rect pair side, cells ((j, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega)
      (rect,pair)), side) ∈ active) ∧
    (∀ j k edge side, cells ((j, prefixOrdinaryPairIndex
      (show (4*6)*2+2*(3*n) ≤ 6*(n+8) by omega) (0,k,edge)), side) ∉ active) ∧
    (∀ j k edge side, cells ((j, prefixOrdinaryPairIndex
      (show (4*6)*2+2*(3*n) ≤ 6*(n+8) by omega) (1,k,edge)), side) ∉ active) := by
  classical
  dsimp only
  let offset := 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)
  let active := activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
  have hactive : active ⊆ packedRectangleSupport hs choice :=
    active_rectangle_support_subset_packed hs choice (fwActiveRectangleLabels n P hP)
  constructor
  · intro j rect pair side
    rw [fw_growth_offset_rectangle_cell offset hoff hs choice gr gc hgr hgc]
    apply Finset.mem_image.mpr
    refine ⟨(btGrowingOffsetRectangle offset hoff (finProdFinEquiv (j,rect)), prefixPairCorner pair side), ?_, rfl⟩
    apply Finset.mem_product.mpr
    constructor
    · apply (fw_active_rectangle_label_mem_iff n P hP _).mpr
      have hv := (finProdFinEquiv (j,rect) : Fin (P * (4*6))).isLt
      dsimp [btGrowingOffsetRectangle, fwActiveRectangleCount, offset]
      omega
    · exact Finset.mem_univ _
  constructor
  · intro j k edge side hmem
    rw [fw_growth_ordinary_row_cell offset hoff hs choice gr gc hgr hgc] at hmem
    have hm : LayerPacking.layerCell (prefixStageLayer gr hgr j k).1
        (prefixStageLayer gr hgr j k).2 (edge,side) ∈ LayerPacking.layersSupport (preRows ++ gr) := by
      apply LayerPacking.layerSupport_subset (prefixStageLayer gr hgr j k) (preRows ++ gr)
      · simp [prefixStageLayer, List.get_mem]
      · change LayerPacking.sequenceCell gr
          (Fin.cast hgr.symm (finProdFinEquiv (j,k)), (edge,side)) ∈ _
        exact LayerPacking.sequenceCell_mem gr _ _
    exact Finset.disjoint_left.mp hrows.reserved_disjoint (hactive hmem) hm
  · intro j k edge side hmem
    rw [fw_growth_ordinary_column_cell offset hoff hs choice gr gc hgr hgc] at hmem
    have hm : (LayerPacking.layerCell (prefixStageLayer gc hgc j k).1
        (prefixStageLayer gc hgc j k).2 (edge,side)).swap ∈
        LayerPacking.transposeCells (LayerPacking.layersSupport (preCols ++ gc)) := by
      apply Finset.mem_image.mpr
      refine ⟨_, ?_, rfl⟩
      apply LayerPacking.layerSupport_subset (prefixStageLayer gc hgc j k) (preCols ++ gc)
      · simp [prefixStageLayer, List.get_mem]
      · change LayerPacking.sequenceCell gc
          (Fin.cast hgc.symm (finProdFinEquiv (j,k)), (edge,side)) ∈ _
        exact LayerPacking.sequenceCell_mem gc _ _
    exact (hcols.transposed_support_safe _ hm).1 (Finset.mem_union_left _ (hactive hmem))

end
end Sude
