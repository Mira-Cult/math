import Sude.FWThetaFamilyWitness
import Sude.FWThetaNetworkWitness
import Sude.FWThetaProjectedFreshWideWitness
import Sude.DoubleBlockSelectedLineIdentity
import Sude.FWGroupedDiagonalMass
import Sude.FWSeedDiagonalOrientation
import Sude.FWWideBalancedPhysicalCenteredGap
import Sude.FWFourFamilyPairInjection

/-! Stage-wise diagonal weight and signed-orientation sums for the grouped
bridge and wide physical double-block families, and the resulting diagonal
difference identity on the ordered square of a theta family witness. -/
namespace Sude
noncomputable section
open scoped BigOperators
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Split a stage's block/pair sum into its 24×2 diagonal rectangle pairs and
its 2×3×n ordinary layer pairs via `fwControllerStagePairBlock`. -/
theorem fw_controller_stage_pair_sum_split (n : ℕ) (F : Fin (3 * (n + 8)) → Fin 2 → ℝ) :
    (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2, F b p) =
    (∑ rect : Fin (4 * 6), ∑ pair : Fin 2, F (Fin.castLE (by omega) rect) pair) +
    (∑ network : Fin 2, ∑ k : Fin 3, ∑ edge : Fin n,
      F (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) (k, edge)) network) := by
  classical
  let e := Equiv.ofBijective (fwControllerStagePairBlock n) (fwControllerStagePairBlock_bijective n)
  calc
    (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2, F b p)
      = ∑ x : Fin (3 * (n + 8)) × Fin 2, F x.1 x.2 := (Fintype.sum_prod_type (fun x => F x.1 x.2)).symm
    _ = ∑ tag : PrefixStagePair 6 3 n, F (e tag).1 (e tag).2 := (e.sum_comp (fun x => F x.1 x.2)).symm
    _ = _ := by simp [e, fwControllerStagePairBlock, Fintype.sum_sum_type, Fintype.sum_prod_type]

/-- Under a balanced 12/12 rectangle choice, the rectangle orientation sum
against half-gaps picks out `-1/2` times the sum over `fwWideSignedGapSlots`. -/
theorem fw_balanced_rectangle_orientation_gap_sum {n L : ℕ}
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (choice : Fin L → Bool)
    (label : Fin (4 * 6) → Fin L)
    (hchoice : ∀ r : Fin (4 * 6), choice (label r) = decide (r.val < 12))
    (G : Fin (3 * (n + 8)) → ℝ) :
    (∑ rect : Fin (4 * 6), ∑ pair : Fin 2,
      (-rectanglePairWeight hs choice (fun c => c ∈ mainCells n) (label rect, pair)) *
        (G (Fin.castLE (by omega) rect) / 2)) =
      -(1 / 2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n true, G b ∧
    (∑ rect : Fin (4 * 6), ∑ pair : Fin 2,
      (-rectanglePairWeight hs choice (fun c => c ∈ antiCells n) (label rect, pair)) *
        (G (Fin.castLE (by omega) rect) / 2)) =
      -(1 / 2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n false, G b := by
  classical
  have hcastTrue (r : Fin 12) :
      (Fin.castLE (by omega : 4 * 6 ≤ 3 * (n + 8)) (Fin.castAdd 12 r : Fin (12 + 12))) =
        fwWideSignedGapSlot n true r := by
    apply Fin.ext
    simp [fwWideSignedGapSlot, fwWideSignedGapRectangle]
  have hcastFalse (r : Fin 12) :
      (Fin.castLE (by omega : 4 * 6 ≤ 3 * (n + 8)) (Fin.natAdd 12 r : Fin (12 + 12))) =
        fwWideSignedGapSlot n false r := by
    apply Fin.ext
    simp [fwWideSignedGapSlot, fwWideSignedGapRectangle]
    omega
  constructor
  · rw [fwWideSignedGapSlots, Finset.sum_image (by
      intro a _ b _ h; exact fw_wide_signed_gap_slot_injective n true h), Finset.mul_sum]
    change (∑ rect : Fin (12 + 12), ∑ pair : Fin 2,
      (-rectanglePairWeight hs choice (fun c => c ∈ mainCells n) (label rect, pair)) *
        (G (Fin.castLE (by omega) rect) / 2)) = _
    rw [Fin.sum_univ_add]
    have h1 : (∑ r : Fin 12, ∑ pair : Fin 2,
        (-rectanglePairWeight hs choice (fun c => c ∈ mainCells n) (label (Fin.castAdd 12 r), pair)) *
          (G (Fin.castLE (by omega) (Fin.castAdd 12 r)) / 2)) =
        ∑ r : Fin 12, -(1 / 2 : ℝ) * G (fwWideSignedGapSlot n true r) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Fin.sum_univ_two, rectanglePairWeight_main hs hL, rectanglePairWeight_main hs hL,
        hchoice (Fin.castAdd 12 r), hcastTrue r]
      simp
      ring
    have h2 : (∑ r : Fin 12, ∑ pair : Fin 2,
        (-rectanglePairWeight hs choice (fun c => c ∈ mainCells n) (label (Fin.natAdd 12 r), pair)) *
          (G (Fin.castLE (by omega) (Fin.natAdd 12 r)) / 2)) = 0 := by
      apply Finset.sum_eq_zero
      intro r _
      rw [Fin.sum_univ_two, rectanglePairWeight_main hs hL, rectanglePairWeight_main hs hL,
        hchoice (Fin.natAdd 12 r)]
      simp
    rw [h1, h2, add_zero]
  · rw [fwWideSignedGapSlots, Finset.sum_image (by
      intro a _ b _ h; exact fw_wide_signed_gap_slot_injective n false h), Finset.mul_sum]
    change (∑ rect : Fin (12 + 12), ∑ pair : Fin 2,
      (-rectanglePairWeight hs choice (fun c => c ∈ antiCells n) (label rect, pair)) *
        (G (Fin.castLE (by omega) rect) / 2)) = _
    rw [Fin.sum_univ_add]
    have h1 : (∑ r : Fin 12, ∑ pair : Fin 2,
        (-rectanglePairWeight hs choice (fun c => c ∈ antiCells n) (label (Fin.castAdd 12 r), pair)) *
          (G (Fin.castLE (by omega) (Fin.castAdd 12 r)) / 2)) = 0 := by
      apply Finset.sum_eq_zero
      intro r _
      rw [Fin.sum_univ_two, rectanglePairWeight_anti hs hL, rectanglePairWeight_anti hs hL,
        hchoice (Fin.castAdd 12 r)]
      simp
    have h2 : (∑ r : Fin 12, ∑ pair : Fin 2,
        (-rectanglePairWeight hs choice (fun c => c ∈ antiCells n) (label (Fin.natAdd 12 r), pair)) *
          (G (Fin.castLE (by omega) (Fin.natAdd 12 r)) / 2)) =
        ∑ r : Fin 12, -(1 / 2 : ℝ) * G (fwWideSignedGapSlot n false r) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Fin.sum_univ_two, rectanglePairWeight_anti hs hL, rectanglePairWeight_anti hs hL,
        hchoice (Fin.natAdd 12 r), hcastFalse r]
      simp
      ring
    rw [h1, h2, zero_add]

/-- Each bridge stage has unsquared diagonal weight sum equal to 12 on both diagonals. -/
theorem fw_bridge_grouped_stage_diagonal_weight_sum {n L P : ℕ}
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
    (∑ b : Fin (3 * (n + 8)), doubleBlockLineWeight cells (fun c => c ∈ mainCells n) j b) = 12 ∧
    (∑ b : Fin (3 * (n + 8)), doubleBlockLineWeight cells (fun c => c ∈ antiCells n) j b) = 12 := by
  classical
  dsimp only
  let choice := fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth otherChoice
  let cells := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
  have hmass := fw_bridge_grouped_stage_diagonal_mass hrect hseed hwide hgrowth hs hL otherChoice
    br bc sr sc wr wc gr gc hbr hbc reservedRows reservedCols hrows hcols j
  dsimp only at hmass
  have hzero := fun network k edge => fw_bridge_ordinary_diagonal_weight_zero hrect hs choice
    br bc sr sc wr wc gr gc hbr hbc reservedRows reservedCols hrows hcols j network k edge
  have hsq (line : Cell n → Prop)
      (hrect_line : ∀ rect pair,
        rectanglePairWeight hs choice line (prefixRectanglePairSlot hrect ((j, rect), pair)) =
        (rectanglePairWeight hs choice line (prefixRectanglePairSlot hrect ((j, rect), pair))) ^ 2)
      (hord_line : ∀ network k edge,
        physicalPairLineWeight (fwBridgePhysicalPairCells hrect hs choice br bc hbr hbc) line
          (j, fwPrefixToControllerPair n (prefixOrdinaryPairIndex
            (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network, k, edge))) = 0) :
      (∑ b : Fin (3 * (n + 8)), doubleBlockLineWeight cells line j b) =
      (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2, (physicalPairLineWeight cells line (j, b, p)) ^ 2) := by
    have hsum2 : (∑ b : Fin (3 * (n + 8)), doubleBlockLineWeight cells line j b) =
        ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2, physicalPairLineWeight cells line (j, b, p) := by
      apply Finset.sum_congr rfl; intro b _
      exact (Fin.sum_univ_two (fun p => physicalPairLineWeight cells line (j, b, p))).symm
    rw [hsum2, fw_controller_stage_pair_sum_split n (fun b p => physicalPairLineWeight cells line (j, b, p)),
        fw_controller_stage_pair_sum_split n (fun b p => (physicalPairLineWeight cells line (j, b, p)) ^ 2)]
    congr 1
    · apply Finset.sum_congr rfl; intro rect _
      apply Finset.sum_congr rfl; intro pair _
      have heq : physicalPairLineWeight cells line (j, Fin.castLE (by omega) rect, pair) =
          rectanglePairWeight hs choice line (prefixRectanglePairSlot hrect ((j, rect), pair)) := by
        rw [← fw_bridge_reindexed_rectangle_pair_weight hrect hs choice br bc hbr hbc line j rect pair]
        unfold cells fwBridgePhysicalDoubleCells Function.comp
        rw [fwPrefixToControllerPair_diagonal]
        rfl
      rw [heq]
      exact hrect_line rect pair
    · apply Finset.sum_congr rfl; intro network _
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro edge _
      have heq : physicalPairLineWeight cells line
          (j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) (k, edge), network) =
          physicalPairLineWeight (fwBridgePhysicalPairCells hrect hs choice br bc hbr hbc) line
            (j, fwPrefixToControllerPair n (prefixOrdinaryPairIndex
              (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network, k, edge))) := by
        unfold cells fwBridgePhysicalDoubleCells Function.comp
        rw [fwPrefixToControllerPair_ordinary]
        rfl
      rw [heq, hord_line network k edge]
      norm_num
  constructor
  · rw [hsq (fun c => c ∈ mainCells n) (by
      intro rect pair; rw [rectanglePairWeight_main hs hL]; split_ifs <;> norm_num)
      (fun network k edge => (hzero network k edge).1)]
    exact hmass.1
  · rw [hsq (fun c => c ∈ antiCells n) (by
      intro rect pair; rw [rectanglePairWeight_anti hs hL]; split_ifs <;> norm_num)
      (fun network k edge => (hzero network k edge).2)]
    exact hmass.2

/-- Each wide stage has unsquared diagonal weight sum equal to 12 on both diagonals. -/
theorem fw_wide_grouped_stage_diagonal_weight_sum {n L P : ℕ}
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
    (∑ b : Fin (3 * (n + 8)), doubleBlockLineWeight cells (fun c => c ∈ mainCells n) j b) = 12 ∧
    (∑ b : Fin (3 * (n + 8)), doubleBlockLineWeight cells (fun c => c ∈ antiCells n) j b) = 12 := by
  classical
  dsimp only
  let choice := fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth otherChoice
  let cells := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
  have hmass := fw_wide_grouped_stage_diagonal_mass hrect hseed hwide hgrowth hs hL otherChoice
    br bc sr sc wr wc gr gc hwr hwc reservedRows reservedCols hrows hcols j
  dsimp only at hmass
  have hzero := fun network k edge => fw_wide_ordinary_diagonal_weight_zero hwide hs choice
    br bc sr sc wr wc gr gc hwr hwc reservedRows reservedCols hrows hcols j network k edge
  have hsq (line : Cell n → Prop)
      (hrect_line : ∀ rect pair,
        rectanglePairWeight hs choice line (fwWideOffsetPairSlot hwide ((j, rect), pair)) =
        (rectanglePairWeight hs choice line (fwWideOffsetPairSlot hwide ((j, rect), pair))) ^ 2)
      (hord_line : ∀ network k edge,
        physicalPairLineWeight (fwWidePhysicalPairCells hwide hs choice wr wc hwr hwc) line
          (j, fwPrefixToControllerPair n (prefixOrdinaryPairIndex
            (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network, k, edge))) = 0) :
      (∑ b : Fin (3 * (n + 8)), doubleBlockLineWeight cells line j b) =
      (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2, (physicalPairLineWeight cells line (j, b, p)) ^ 2) := by
    have hsum2 : (∑ b : Fin (3 * (n + 8)), doubleBlockLineWeight cells line j b) =
        ∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2, physicalPairLineWeight cells line (j, b, p) := by
      apply Finset.sum_congr rfl; intro b _
      exact (Fin.sum_univ_two (fun p => physicalPairLineWeight cells line (j, b, p))).symm
    rw [hsum2, fw_controller_stage_pair_sum_split n (fun b p => physicalPairLineWeight cells line (j, b, p)),
        fw_controller_stage_pair_sum_split n (fun b p => (physicalPairLineWeight cells line (j, b, p)) ^ 2)]
    congr 1
    · apply Finset.sum_congr rfl; intro rect _
      apply Finset.sum_congr rfl; intro pair _
      have heq : physicalPairLineWeight cells line (j, Fin.castLE (by omega) rect, pair) =
          rectanglePairWeight hs choice line (fwWideOffsetPairSlot hwide ((j, rect), pair)) := by
        rw [← fw_wide_reindexed_rectangle_pair_weight hwide hs choice wr wc hwr hwc line j rect pair]
        unfold cells fwWidePhysicalDoubleCells Function.comp
        rw [fwPrefixToControllerPair_diagonal]
        rfl
      rw [heq]
      exact hrect_line rect pair
    · apply Finset.sum_congr rfl; intro network _
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro edge _
      have heq : physicalPairLineWeight cells line
          (j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) (k, edge), network) =
          physicalPairLineWeight (fwWidePhysicalPairCells hwide hs choice wr wc hwr hwc) line
            (j, fwPrefixToControllerPair n (prefixOrdinaryPairIndex
              (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network, k, edge))) := by
        unfold cells fwWidePhysicalDoubleCells Function.comp
        rw [fwPrefixToControllerPair_ordinary]
        rfl
      rw [heq, hord_line network k edge]
      norm_num
  constructor
  · rw [hsq (fun c => c ∈ mainCells n) (by
      intro rect pair; rw [rectanglePairWeight_main hs hL]; split_ifs <;> norm_num)
      (fun network k edge => (hzero network k edge).1)]
    exact hmass.1
  · rw [hsq (fun c => c ∈ antiCells n) (by
      intro rect pair; rw [rectanglePairWeight_anti hs hL]; split_ifs <;> norm_num)
      (fun network k edge => (hzero network k edge).2)]
    exact hmass.2

/-- Each bridge stage's signed orientation sum against half-gaps equals
`-1/2` times the sum of gaps over `fwWideSignedGapSlots`. -/
theorem fw_bridge_grouped_stage_diagonal_orientation_sum {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers reservedCols (((bc ++ sc) ++ wc) ++ gc))
    (G : Fin (3 * (n + 8)) → ℝ) (j : Fin 5) :
    let choice := fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth otherChoice
    let cells := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      physicalPairLineOrientation cells (fun c => c ∈ mainCells n) (j, b, p) * (G b / 2)) =
      -(1 / 2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n true, G b ∧
    (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      physicalPairLineOrientation cells (fun c => c ∈ antiCells n) (j, b, p) * (G b / 2)) =
      -(1 / 2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n false, G b := by
  classical
  dsimp only
  let choice := fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth otherChoice
  let cells := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
  let label := fun rect : Fin (4 * 6) => bridgeDiagonalRectangle hrect (finProdFinEquiv (j, rect))
  have hbal := fw_balanced_rectangle_orientation_gap_sum hs hL choice label
    (fwBridgeSeedWideGrowthChoice_bridge hrect hseed hwide hgrowth otherChoice j) G
  have hcell (rect : Fin (4 * 6)) (pair : Fin 2) (side : Bool) :
      cells ((j, Fin.castLE (by omega) rect, pair), side) =
        packedRectangleCorner hs choice (label rect, prefixPairCorner pair side) := by
    have h := fw_bridge_reindexed_diagonal_cell hrect hs choice br bc hbr hbc j rect pair side
    rw [fwPrefixToControllerPair_diagonal] at h
    exact h
  have hord (network : Fin 2) (k : Fin 3) (edge : Fin n) (side : Bool) :
      cells ((j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) (k, edge), network), side) ∉ mainCells n ∧
      cells ((j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) (k, edge), network), side) ∉ antiCells n := by
    have h := fw_bridge_ordinary_cell_off_diagonals hrect hs choice br bc sr sc wr wc gr gc
      hbr hbc reservedRows reservedCols hrows hcols j network k edge side
    dsimp only at h
    rw [fwPrefixToControllerPair_ordinary] at h
    exact h
  constructor
  · rw [fw_controller_stage_pair_sum_split n]
    have h2 : (∑ network : Fin 2, ∑ k : Fin 3, ∑ edge : Fin n,
        physicalPairLineOrientation cells (fun c => c ∈ mainCells n)
          (j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) (k, edge), network) *
          (G (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) (k, edge)) / 2)) = 0 := by
      apply Finset.sum_eq_zero; intro network _
      apply Finset.sum_eq_zero; intro k _
      apply Finset.sum_eq_zero; intro edge _
      have hf := (hord network k edge false).1
      have ht := (hord network k edge true).1
      unfold physicalPairLineOrientation
      rw [if_neg ht, if_neg hf]
      ring
    rw [h2, add_zero, ← hbal.1]
    apply Finset.sum_congr rfl; intro rect _
    apply Finset.sum_congr rfl; intro pair _
    congr 1
    have hor := fw_seed_rectangle_main_orientation_eq_neg_weight hs hL choice (label rect) pair
    unfold physicalPairLineOrientation at hor ⊢
    dsimp only [cells, choice] at hcell ⊢
    rw [hcell rect pair true, hcell rect pair false]
    exact hor
  · rw [fw_controller_stage_pair_sum_split n]
    have h2 : (∑ network : Fin 2, ∑ k : Fin 3, ∑ edge : Fin n,
        physicalPairLineOrientation cells (fun c => c ∈ antiCells n)
          (j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) (k, edge), network) *
          (G (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) (k, edge)) / 2)) = 0 := by
      apply Finset.sum_eq_zero; intro network _
      apply Finset.sum_eq_zero; intro k _
      apply Finset.sum_eq_zero; intro edge _
      have hf := (hord network k edge false).2
      have ht := (hord network k edge true).2
      unfold physicalPairLineOrientation
      rw [if_neg ht, if_neg hf]
      ring
    rw [h2, add_zero, ← hbal.2]
    apply Finset.sum_congr rfl; intro rect _
    apply Finset.sum_congr rfl; intro pair _
    congr 1
    have hor := fw_seed_rectangle_anti_orientation_eq_neg_weight hs hL choice (label rect) pair
    unfold physicalPairLineOrientation at hor ⊢
    dsimp only [cells, choice] at hcell ⊢
    rw [hcell rect pair true, hcell rect pair false]
    exact hor

/-- Each wide stage's signed orientation sum against half-gaps equals
`-1/2` times the sum of gaps over `fwWideSignedGapSlots`. -/
theorem fw_wide_grouped_stage_diagonal_orientation_sum {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers reservedCols (((bc ++ sc) ++ wc) ++ gc))
    (G : Fin (3 * (n + 8)) → ℝ) (j : Fin (3 * (n / 450))) :
    let choice := fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth otherChoice
    let cells := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      physicalPairLineOrientation cells (fun c => c ∈ mainCells n) (j, b, p) * (G b / 2)) =
      -(1 / 2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n true, G b ∧
    (∑ b : Fin (3 * (n + 8)), ∑ p : Fin 2,
      physicalPairLineOrientation cells (fun c => c ∈ antiCells n) (j, b, p) * (G b / 2)) =
      -(1 / 2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n false, G b := by
  classical
  dsimp only
  let choice := fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth otherChoice
  let cells := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
  let label := fun rect : Fin (4 * 6) => fwWideRectangle hwide (finProdFinEquiv (j, rect))
  have hbal := fw_balanced_rectangle_orientation_gap_sum hs hL choice label
    (fwBridgeSeedWideGrowthChoice_wide hrect hseed hwide hgrowth otherChoice j) G
  have hcell (rect : Fin (4 * 6)) (pair : Fin 2) (side : Bool) :
      cells ((j, Fin.castLE (by omega) rect, pair), side) =
        packedRectangleCorner hs choice (label rect, prefixPairCorner pair side) := by
    have h := fw_wide_reindexed_diagonal_cell hwide hs choice wr wc hwr hwc j rect pair side
    rw [fwPrefixToControllerPair_diagonal] at h
    exact h
  have hord (network : Fin 2) (k : Fin 3) (edge : Fin n) (side : Bool) :
      cells ((j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) (k, edge), network), side) ∉ mainCells n ∧
      cells ((j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) (k, edge), network), side) ∉ antiCells n := by
    have h := fw_wide_ordinary_cell_off_diagonals hwide hs choice br bc sr sc wr wc gr gc
      hwr hwc reservedRows reservedCols hrows hcols j network k edge side
    dsimp only at h
    rw [fwPrefixToControllerPair_ordinary] at h
    exact h
  constructor
  · rw [fw_controller_stage_pair_sum_split n]
    have h2 : (∑ network : Fin 2, ∑ k : Fin 3, ∑ edge : Fin n,
        physicalPairLineOrientation cells (fun c => c ∈ mainCells n)
          (j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) (k, edge), network) *
          (G (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) (k, edge)) / 2)) = 0 := by
      apply Finset.sum_eq_zero; intro network _
      apply Finset.sum_eq_zero; intro k _
      apply Finset.sum_eq_zero; intro edge _
      have hf := (hord network k edge false).1
      have ht := (hord network k edge true).1
      unfold physicalPairLineOrientation
      rw [if_neg ht, if_neg hf]
      ring
    rw [h2, add_zero, ← hbal.1]
    apply Finset.sum_congr rfl; intro rect _
    apply Finset.sum_congr rfl; intro pair _
    congr 1
    have hor := fw_seed_rectangle_main_orientation_eq_neg_weight hs hL choice (label rect) pair
    unfold physicalPairLineOrientation at hor ⊢
    dsimp only [cells, choice] at hcell ⊢
    rw [hcell rect pair true, hcell rect pair false]
    exact hor
  · rw [fw_controller_stage_pair_sum_split n]
    have h2 : (∑ network : Fin 2, ∑ k : Fin 3, ∑ edge : Fin n,
        physicalPairLineOrientation cells (fun c => c ∈ antiCells n)
          (j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) (k, edge), network) *
          (G (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) (k, edge)) / 2)) = 0 := by
      apply Finset.sum_eq_zero; intro network _
      apply Finset.sum_eq_zero; intro k _
      apply Finset.sum_eq_zero; intro edge _
      have hf := (hord network k edge false).2
      have ht := (hord network k edge true).2
      unfold physicalPairLineOrientation
      rw [if_neg ht, if_neg hf]
      ring
    rw [h2, add_zero, ← hbal.2]
    apply Finset.sum_congr rfl; intro rect _
    apply Finset.sum_congr rfl; intro pair _
    congr 1
    have hor := fw_seed_rectangle_anti_orientation_eq_neg_weight hs hL choice (label rect) pair
    unfold physicalPairLineOrientation at hor ⊢
    dsimp only [cells, choice] at hcell ⊢
    rw [hcell rect pair true, hcell rect pair false]
    exact hor

end
end Sude
