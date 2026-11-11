import Sude.FWSeedExistingReallocation
import Sude.PrefixDiagonalSlotWeights
import Sude.RectangleDiagonalIncidence
import Sude.FWSeedOffsetDiagonalWeights

/-! Physical diagonal incidence for the actual offset seed pair slots. -/
namespace Sude
noncomputable section

/-- At each seed rectangle label, the reindexed physical slot is the actual
FW offset rectangle corner. -/
theorem fw_seed_existing_rectangle_cell {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (j : Fin 16) (rect : Fin (4 * 6))
    (pair : Fin 2) (side : Bool) :
    fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      ((j, prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect, pair)), side) =
    packedRectangleCorner hs choice (fwSeedRectangle hseed (finProdFinEquiv (j, rect)), prefixPairCorner pair side) := by
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let e := Equiv.ofBijective (prefixPhysicalInput (P := 16) hfit hdiag) (fwSeedPhysicalInput_bijective n)
  have he : e.symm ((j, prefixDiagonalPairIndex hdiag (rect, pair)), side) =
      Sum.inl (finProdFinEquiv (j, rect), prefixPairCorner pair side) := by
    apply e.symm_apply_eq.mpr
    simpa [e, prefixPhysicalInput] using (prefixRectangleInput_pair hdiag j rect pair side).symm
  change btGrowingOffsetCells (5 * (4 * 6)) hseed hs choice sr sc hsr hsc
    (e.symm ((j, prefixDiagonalPairIndex hdiag (rect, pair)), side)) = _
  rw [he]
  rfl

/-- Main/anti seed-rectangle incidence is exactly its physical pair weight. -/
theorem fw_seed_existing_rectangle_weight {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (j : Fin 16) (rect : Fin (4 * 6)) (pair : Fin 2) :
    physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
      (fun c => c ∈ mainCells n)
      (j, prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect, pair)) =
    if pair = 0 ∧ choice (fwSeedRectangle hseed (finProdFinEquiv (j, rect))) = true then 1 else 0 := by
  classical
  have hp := rectanglePairWeight_main hs hL choice (fwSeedRectangle hseed (finProdFinEquiv (j, rect))) pair
  unfold physicalPairLineWeight
  rw [fw_seed_existing_rectangle_cell hseed hs choice sr sc hsr hsc j rect pair false,
    fw_seed_existing_rectangle_cell hseed hs choice sr sc hsr hsc j rect pair true]
  exact hp

/-- Anti seed-rectangle incidence is exactly its physical pair weight. -/
theorem fw_seed_existing_rectangle_anti_weight {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (j : Fin 16) (rect : Fin (4 * 6)) (pair : Fin 2) :
    physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
      (fun c => c ∈ antiCells n)
      (j, prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect, pair)) =
    if pair = 0 ∧ choice (fwSeedRectangle hseed (finProdFinEquiv (j, rect))) = false then 1 else 0 := by
  classical
  have hp := rectanglePairWeight_anti hs hL choice (fwSeedRectangle hseed (finProdFinEquiv (j, rect))) pair
  unfold physicalPairLineWeight
  rw [fw_seed_existing_rectangle_cell hseed hs choice sr sc hsr hsc j rect pair false,
    fw_seed_existing_rectangle_cell hseed hs choice sr sc hsr hsc j rect pair true]
  exact hp

/-- Ordinary row-network pair endpoints are off both diagonals. -/
theorem fw_seed_existing_row_off_diagonals {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (reserved : Finset (Cell n))
    (packed : LayerPacking.PackedLayers reserved sr)
    (j : Fin 16) (k : Fin 3) (edge : Fin n) (side : Bool) :
    fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      ((j, prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (0, k, edge)), side) ∉ mainCells n ∧
    fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      ((j, prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (0, k, edge)), side) ∉ antiCells n := by
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let e := Equiv.ofBijective (prefixPhysicalInput (P := 16) hfit hdiag) (fwSeedPhysicalInput_bijective n)
  have he : e.symm ((j, prefixOrdinaryPairIndex hfit (0, k, edge)), side) =
      Sum.inr (Sum.inl (finProdFinEquiv (j, k), (edge, side))) := by
    apply e.symm_apply_eq.mpr
    simpa [e, prefixPhysicalInput] using (prefixStageLayer_networkInput hfit rfl 0 j k edge side).symm
  have hc : fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      ((j, prefixOrdinaryPairIndex hfit (0, k, edge)), side) =
    LayerPacking.layerCell (prefixStageLayer sr hsr j k).1
      (prefixStageLayer sr hsr j k).2 (edge, side) := by
    change btGrowingOffsetCells (5 * (4 * 6)) hseed hs choice sr sc hsr hsc
      (e.symm ((j, prefixOrdinaryPairIndex hfit (0, k, edge)), side)) = _
    rw [he]
    exact prefixStageLayer_sequenceCell sr hsr j k edge side
  rw [hc]
  exact prefixStageLayer_off_diagonals sr hsr reserved packed j k edge side

/-- Ordinary transposed column-network pair endpoints are off both diagonals. -/
theorem fw_seed_existing_column_off_diagonals {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (reserved : Finset (Cell n))
    (packed : LayerPacking.PackedLayers reserved sc)
    (j : Fin 16) (k : Fin 3) (edge : Fin n) (side : Bool) :
    fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      ((j, prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (1, k, edge)), side) ∉ mainCells n ∧
    fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      ((j, prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (1, k, edge)), side) ∉ antiCells n := by
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let e := Equiv.ofBijective (prefixPhysicalInput (P := 16) hfit hdiag) (fwSeedPhysicalInput_bijective n)
  have he : e.symm ((j, prefixOrdinaryPairIndex hfit (1, k, edge)), side) =
      Sum.inr (Sum.inr (finProdFinEquiv (j, k), (edge, side))) := by
    apply e.symm_apply_eq.mpr
    simpa [e, prefixPhysicalInput] using (prefixStageLayer_networkInput hfit rfl 1 j k edge side).symm
  have hc : fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      ((j, prefixOrdinaryPairIndex hfit (1, k, edge)), side) =
    (LayerPacking.layerCell (prefixStageLayer sc hsc j k).1
      (prefixStageLayer sc hsc j k).2 (edge, side)).swap := by
    change btGrowingOffsetCells (5 * (4 * 6)) hseed hs choice sr sc hsr hsc
      (e.symm ((j, prefixOrdinaryPairIndex hfit (1, k, edge)), side)) = _
    rw [he]
    exact congrArg Prod.swap (prefixStageLayer_sequenceCell sc hsc j k edge side)
  rw [hc]
  exact prefixStageLayer_swap_off_diagonals sc hsc reserved packed j k edge side


/-- Every actual seed pair-slot main-diagonal weight has the stated offset
rectangle or off-diagonal ordinary-network incidence. -/
theorem fw_seed_existing_main_weight_at_label {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows sr)
    (packedCols : LayerPacking.PackedLayers reservedCols sc)
    (j : Fin 16) (tag : PrefixStagePair 6 3 n) :
    physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
      (fun c => c ∈ mainCells n)
      (j, prefixStagePairSlot
        (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) tag) =
    fwSeedOffsetDiagonalIncidence hseed hs choice (fun c => c ∈ mainCells n) j tag := by
  classical
  cases tag with
  | inl x =>
    rcases x with ⟨rect, pair⟩
    simp only [prefixStagePairSlot, fwSeedOffsetDiagonalIncidence]
    unfold physicalPairLineWeight rectanglePairWeight
    rw [fw_seed_existing_rectangle_cell hseed hs choice sr sc hsr hsc j rect pair false,
      fw_seed_existing_rectangle_cell hseed hs choice sr sc hsr hsc j rect pair true]
  | inr x =>
    rcases x with ⟨network, layer, edge⟩
    fin_cases network
    · have hf := (fw_seed_existing_row_off_diagonals hseed hs choice sr sc hsr hsc reservedRows packedRows j layer edge false).1
      have ht := (fw_seed_existing_row_off_diagonals hseed hs choice sr sc hsr hsc reservedRows packedRows j layer edge true).1
      simp [prefixStagePairSlot, fwSeedOffsetDiagonalIncidence, physicalPairLineWeight, hf, ht]
    · have hf := (fw_seed_existing_column_off_diagonals hseed hs choice sr sc hsr hsc reservedCols packedCols j layer edge false).1
      have ht := (fw_seed_existing_column_off_diagonals hseed hs choice sr sc hsr hsc reservedCols packedCols j layer edge true).1
      simp [prefixStagePairSlot, fwSeedOffsetDiagonalIncidence, physicalPairLineWeight, hf, ht]

/-- Every actual seed pair-slot anti-diagonal weight has the stated offset
rectangle or off-diagonal ordinary-network incidence. -/
theorem fw_seed_existing_anti_weight_at_label {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows sr)
    (packedCols : LayerPacking.PackedLayers reservedCols sc)
    (j : Fin 16) (tag : PrefixStagePair 6 3 n) :
    physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
      (fun c => c ∈ antiCells n)
      (j, prefixStagePairSlot
        (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) tag) =
    fwSeedOffsetDiagonalIncidence hseed hs choice (fun c => c ∈ antiCells n) j tag := by
  classical
  cases tag with
  | inl x =>
    rcases x with ⟨rect, pair⟩
    simp only [prefixStagePairSlot, fwSeedOffsetDiagonalIncidence]
    unfold physicalPairLineWeight rectanglePairWeight
    rw [fw_seed_existing_rectangle_cell hseed hs choice sr sc hsr hsc j rect pair false,
      fw_seed_existing_rectangle_cell hseed hs choice sr sc hsr hsc j rect pair true]
  | inr x =>
    rcases x with ⟨network, layer, edge⟩
    fin_cases network
    · have hf := (fw_seed_existing_row_off_diagonals hseed hs choice sr sc hsr hsc reservedRows packedRows j layer edge false).2
      have ht := (fw_seed_existing_row_off_diagonals hseed hs choice sr sc hsr hsc reservedRows packedRows j layer edge true).2
      simp [prefixStagePairSlot, fwSeedOffsetDiagonalIncidence, physicalPairLineWeight, hf, ht]
    · have hf := (fw_seed_existing_column_off_diagonals hseed hs choice sr sc hsr hsc reservedCols packedCols j layer edge false).2
      have ht := (fw_seed_existing_column_off_diagonals hseed hs choice sr sc hsr hsc reservedCols packedCols j layer edge true).2
      simp [prefixStagePairSlot, fwSeedOffsetDiagonalIncidence, physicalPairLineWeight, hf, ht]


/-- The actual offset seed pair cells have exactly twelve squared
main-diagonal incidences at every stage. -/
theorem fw_seed_existing_main_squared_sum {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows sr)
    (packedCols : LayerPacking.PackedLayers reservedCols sc) (j : Fin 16) :
    ∑ q : Fin (6 * (n + 8)),
      (physicalPairLineWeight (fwSeedExistingPairCells hseed hs
        (fwBridgeSeedRectangleChoice hrect hseed otherChoice) sr sc hsr hsc)
        (fun c => c ∈ mainCells n) (j, q)) ^ 2 = 12 := by
  classical
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let hexact : (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega
  let e := Equiv.ofBijective (prefixStagePairSlot hfit hdiag)
    (prefixStagePairSlot_bijective hfit hdiag hexact)
  let choice := fwBridgeSeedRectangleChoice hrect hseed otherChoice
  let w := fun q : Fin (6 * (n + 8)) => physicalPairLineWeight
    (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) (fun c => c ∈ mainCells n) (j, q)
  calc
    ∑ q, w q ^ 2 = ∑ tag : PrefixStagePair 6 3 n, w (e tag) ^ 2 :=
      (e.sum_comp (fun q => w q ^ 2)).symm
    _ = fwSeedOffsetRectangleStageInvoice hseed hs choice (fun c => c ∈ mainCells n) j := by
      simp only [w, e, Equiv.ofBijective_apply, fw_seed_existing_main_weight_at_label
        hseed hs choice sr sc hsr hsc reservedRows reservedCols packedRows packedCols,
        fwSeedOffsetDiagonalIncidence, fwSeedOffsetRectangleStageInvoice,
        Fintype.sum_sum_type, Fintype.sum_prod_type]
      simp
    _ = 12 := fw_seed_offset_main_stage_invoice hrect hseed hs hL otherChoice j


/-- The actual offset seed pair cells have exactly twelve squared
antidiagonal incidences at every stage. -/
theorem fw_seed_existing_anti_squared_sum {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows sr)
    (packedCols : LayerPacking.PackedLayers reservedCols sc) (j : Fin 16) :
    ∑ q : Fin (6 * (n + 8)),
      (physicalPairLineWeight (fwSeedExistingPairCells hseed hs
        (fwBridgeSeedRectangleChoice hrect hseed otherChoice) sr sc hsr hsc)
        (fun c => c ∈ antiCells n) (j, q)) ^ 2 = 12 := by
  classical
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let hexact : (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega
  let e := Equiv.ofBijective (prefixStagePairSlot hfit hdiag)
    (prefixStagePairSlot_bijective hfit hdiag hexact)
  let choice := fwBridgeSeedRectangleChoice hrect hseed otherChoice
  let w := fun q : Fin (6 * (n + 8)) => physicalPairLineWeight
    (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) (fun c => c ∈ antiCells n) (j, q)
  calc
    ∑ q, w q ^ 2 = ∑ tag : PrefixStagePair 6 3 n, w (e tag) ^ 2 :=
      (e.sum_comp (fun q => w q ^ 2)).symm
    _ = fwSeedOffsetRectangleStageInvoice hseed hs choice (fun c => c ∈ antiCells n) j := by
      simp only [w, e, Equiv.ofBijective_apply, fw_seed_existing_anti_weight_at_label
        hseed hs choice sr sc hsr hsc reservedRows reservedCols packedRows packedCols,
        fwSeedOffsetDiagonalIncidence, fwSeedOffsetRectangleStageInvoice,
        Fintype.sum_sum_type, Fintype.sum_prod_type]
      simp
    _ = 12 := fw_seed_offset_anti_stage_invoice hrect hseed hs hL otherChoice j


/-- The actual main-diagonal physical slot invoice, weighted by any supplied
stage widths. This is an incidence identity, not an allocation bound. -/
theorem fw_seed_existing_main_weighted_invoice {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows sr)
    (packedCols : LayerPacking.PackedLayers reservedCols sc) (width : Fin 16 → ℝ) :
    (∑ j, (width j) ^ 2 * ∑ q : Fin (6 * (n + 8)),
      (physicalPairLineWeight (fwSeedExistingPairCells hseed hs
        (fwBridgeSeedRectangleChoice hrect hseed otherChoice) sr sc hsr hsc)
        (fun c => c ∈ mainCells n) (j, q)) ^ 2) = 12 * ∑ j, (width j) ^ 2 := by
  simp_rw [fw_seed_existing_main_squared_sum hrect hseed hs hL otherChoice
    sr sc hsr hsc reservedRows reservedCols packedRows packedCols]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The corresponding actual antidiagonal physical slot invoice. -/
theorem fw_seed_existing_anti_weighted_invoice {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows sr)
    (packedCols : LayerPacking.PackedLayers reservedCols sc) (width : Fin 16 → ℝ) :
    (∑ j, (width j) ^ 2 * ∑ q : Fin (6 * (n + 8)),
      (physicalPairLineWeight (fwSeedExistingPairCells hseed hs
        (fwBridgeSeedRectangleChoice hrect hseed otherChoice) sr sc hsr hsc)
        (fun c => c ∈ antiCells n) (j, q)) ^ 2) = 12 * ∑ j, (width j) ^ 2 := by
  simp_rw [fw_seed_existing_anti_squared_sum hrect hseed hs hL otherChoice
    sr sc hsr hsc reservedRows reservedCols packedRows packedCols]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end Sude
