import Sude.FWBalancedDiagonalRectangleInvoice
import Sude.FWOrdinaryDiagonalAvoidance
import Sude.FWGroupedRowColumnMass

/-! Exact grouped physical diagonal pair-incidence masses under the actual
balanced FW rectangle choice and supplied joint layer packings. -/

namespace Sude
noncomputable section

/-- With the actual balanced FW choice and supplied joint packings, each
bridge stage has exactly twelve squared pair incidences on each diagonal. -/
theorem fw_bridge_grouped_stage_diagonal_mass {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers reservedCols (((bc ++ sc) ++ wc) ++ gc))
    (j : Fin 5) :
    let choice := fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth otherChoice
    let cells := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight cells (fun c => c ∈ mainCells n) (j,b,p)) ^ 2) = 12 ∧
    (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight cells (fun c => c ∈ antiCells n) (j,b,p)) ^ 2) = 12 := by
  classical
  dsimp only
  let choice := fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth otherChoice
  have hrects := fw_bridge_physical_balanced_diagonal_invoice hrect hseed hwide hgrowth hs hL
    otherChoice br bc hbr hbc j
  have hzero := fun network k edge => fw_bridge_ordinary_diagonal_weight_zero hrect hs choice
    br bc sr sc wr wc gr gc hbr hbc reservedRows reservedCols hrows hcols j network k edge
  constructor
  · change (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwBridgePhysicalPairCells hrect hs choice br bc hbr hbc ∘ fwBlockPairIndex 5 n)
        (fun c => c ∈ mainCells n) (j,b,p)) ^ 2) = 12
    rw [fw_grouped_stage_mass_split]
    simp_rw [(hzero _ _ _).1]
    simpa using hrects.1
  · change (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwBridgePhysicalPairCells hrect hs choice br bc hbr hbc ∘ fwBlockPairIndex 5 n)
        (fun c => c ∈ antiCells n) (j,b,p)) ^ 2) = 12
    rw [fw_grouped_stage_mass_split]
    simp_rw [(hzero _ _ _).2]
    simpa using hrects.2

/-- The analogous exact per-stage diagonal masses for the actual offset wide
rectangle family and the same supplied joint packings. -/
theorem fw_wide_grouped_stage_diagonal_mass {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers reservedCols (((bc ++ sc) ++ wc) ++ gc))
    (j : Fin (3 * (n / 450))) :
    let choice := fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth otherChoice
    let cells := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight cells (fun c => c ∈ mainCells n) (j,b,p)) ^ 2) = 12 ∧
    (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight cells (fun c => c ∈ antiCells n) (j,b,p)) ^ 2) = 12 := by
  classical
  dsimp only
  let choice := fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth otherChoice
  have hrects := fw_wide_physical_balanced_diagonal_invoice hrect hseed hwide hgrowth hs hL
    otherChoice wr wc hwr hwc j
  have hzero := fun network k edge => fw_wide_ordinary_diagonal_weight_zero hwide hs choice
    br bc sr sc wr wc gr gc hwr hwc reservedRows reservedCols hrows hcols j network k edge
  constructor
  · change (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwWidePhysicalPairCells hwide hs choice wr wc hwr hwc ∘
        fwBlockPairIndex (3 * (n / 450)) n) (fun c => c ∈ mainCells n) (j,b,p)) ^ 2) = 12
    rw [fw_grouped_stage_mass_split]
    simp_rw [(hzero _ _ _).1]
    simpa using hrects.1
  · change (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight (fwWidePhysicalPairCells hwide hs choice wr wc hwr hwc ∘
        fwBlockPairIndex (3 * (n / 450)) n) (fun c => c ∈ antiCells n) (j,b,p)) ^ 2) = 12
    rw [fw_grouped_stage_mass_split]
    simp_rw [(hzero _ _ _).2]
    simpa using hrects.2


/-- Exact full grouped bridge and wide diagonal masses, under the same
balanced choice and the supplied joint row and column packings. -/
theorem fw_joint_bridge_wide_grouped_diagonal_mass {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers reservedCols (((bc ++ sc) ++ wc) ++ gc)) :
    let choice := fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth otherChoice
    let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    (∑ j : Fin 5, ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight bridge (fun c => c ∈ mainCells n) (j,b,p)) ^ 2) = 12 * 5 ∧
    (∑ j : Fin 5, ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight bridge (fun c => c ∈ antiCells n) (j,b,p)) ^ 2) = 12 * 5 ∧
    (∑ j : Fin (3 * (n / 450)), ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight wide (fun c => c ∈ mainCells n) (j,b,p)) ^ 2) =
        12 * ((3 * (n / 450) : ℕ) : ℝ) ∧
    (∑ j : Fin (3 * (n / 450)), ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      (physicalPairLineWeight wide (fun c => c ∈ antiCells n) (j,b,p)) ^ 2) =
        12 * ((3 * (n / 450) : ℕ) : ℝ) := by
  classical
  dsimp only
  have hb := fun j => fw_bridge_grouped_stage_diagonal_mass hrect hseed hwide hgrowth hs hL
    otherChoice br bc sr sc wr wc gr gc hbr hbc reservedRows reservedCols hrows hcols j
  have hw := fun j => fw_wide_grouped_stage_diagonal_mass hrect hseed hwide hgrowth hs hL
    otherChoice br bc sr sc wr wc gr gc hwr hwc reservedRows reservedCols hrows hcols j
  constructor
  · simp_rw [(hb _).1]; norm_num
  constructor
  · simp_rw [(hb _).2]; norm_num
  constructor
  · simp_rw [(hw _).1]; simp [mul_comm]
  · simp_rw [(hw _).2]; simp [mul_comm]

end
end Sude
