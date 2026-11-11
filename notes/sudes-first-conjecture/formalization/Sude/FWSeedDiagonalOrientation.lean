import Sude.FWSeedOffsetActualDiagonal

/-! Exact signed orientation for the prescribed 12/12 seed diagonals. This
is incidence geometry, not a statement about diagonal sums or primality. -/
namespace Sude
noncomputable section
open scoped BigOperators

theorem fw_seed_rectangle_main_orientation_eq_neg_weight {L n : ℕ} (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (rect : Fin L) (pair : Fin 2) :
    physicalPairLineOrientation (fun x : Fin 2 × Bool =>
      packedRectangleCorner hs choice (rect, prefixPairCorner x.1 x.2))
        (fun c => c ∈ mainCells n) pair =
      -rectanglePairWeight hs choice (fun c => c ∈ mainCells n) (rect,pair) := by
  have h01 := RectanglePacking.firstRow_secondColumn_off_diagonals hs hL choice rect
  have h10 := RectanglePacking.secondRow_firstColumn_off_diagonals hs hL choice rect
  have h11 := RectanglePacking.secondRow_secondColumn_off_diagonals hs hL choice rect
  fin_cases pair <;> simp [physicalPairLineOrientation, rectanglePairWeight, prefixPairCorner,
    packedRectangleCorner, h01.1, h10.1, h11.1]

theorem fw_seed_rectangle_anti_orientation_eq_neg_weight {L n : ℕ} (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (rect : Fin L) (pair : Fin 2) :
    physicalPairLineOrientation (fun x : Fin 2 × Bool =>
      packedRectangleCorner hs choice (rect, prefixPairCorner x.1 x.2))
        (fun c => c ∈ antiCells n) pair =
      -rectanglePairWeight hs choice (fun c => c ∈ antiCells n) (rect,pair) := by
  have h01 := RectanglePacking.firstRow_secondColumn_off_diagonals hs hL choice rect
  have h10 := RectanglePacking.secondRow_firstColumn_off_diagonals hs hL choice rect
  have h11 := RectanglePacking.secondRow_secondColumn_off_diagonals hs hL choice rect
  fin_cases pair <;> simp [physicalPairLineOrientation, rectanglePairWeight, prefixPairCorner,
    packedRectangleCorner, h01.2, h10.2, h11.2]

theorem fw_seed_actual_rectangle_main_orientation {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (j : Fin 16) (rect : Fin (4 * 6)) (pair : Fin 2) :
    physicalPairLineOrientation (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun c => c ∈ mainCells n)
        (j, prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect, pair)) =
      -(rectanglePairWeight hs choice (fun c => c ∈ mainCells n)
        (fwSeedRectangle hseed (finProdFinEquiv (j,rect)), pair)) ^ 2 := by
  have h := fw_seed_rectangle_main_orientation_eq_neg_weight hs hL choice
    (fwSeedRectangle hseed (finProdFinEquiv (j,rect))) pair
  have hh : physicalPairLineOrientation (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun c => c ∈ mainCells n)
        (j, prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect, pair)) =
      -rectanglePairWeight hs choice (fun c => c ∈ mainCells n)
        (fwSeedRectangle hseed (finProdFinEquiv (j,rect)), pair) := by
    unfold physicalPairLineOrientation
    rw [fw_seed_existing_rectangle_cell hseed hs choice sr sc hsr hsc j rect pair true,
      fw_seed_existing_rectangle_cell hseed hs choice sr sc hsr hsc j rect pair false]
    simpa [physicalPairLineOrientation] using h
  rw [hh, rectanglePairWeight_main hs hL]
  split_ifs <;> norm_num

theorem fw_seed_actual_rectangle_main_stage_orientation {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (j : Fin 16) :
    (∑ rect : Fin (4 * 6), ∑ pair : Fin 2,
      physicalPairLineOrientation (fwSeedExistingPairCells hseed hs
        (fwBridgeSeedRectangleChoice hrect hseed otherChoice) sr sc hsr hsc)
        (fun c => c ∈ mainCells n)
        (j, prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect, pair))) = -12 := by
  simp_rw [fw_seed_actual_rectangle_main_orientation hseed hs hL]
  simp_rw [Finset.sum_neg_distrib]
  have h := fw_seed_offset_main_stage_invoice hrect hseed hs hL otherChoice j
  change (∑ rect : Fin (4 * 6), ∑ pair : Fin 2,
    rectanglePairWeight hs (fwBridgeSeedRectangleChoice hrect hseed otherChoice)
      (fun c => c ∈ mainCells n) (fwSeedRectangle hseed (finProdFinEquiv (j,rect)),pair) ^ 2) = 12 at h
  rw [h]

theorem fw_seed_actual_rectangle_anti_orientation {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (j : Fin 16) (rect : Fin (4 * 6)) (pair : Fin 2) :
    physicalPairLineOrientation (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun c => c ∈ antiCells n)
        (j, prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect, pair)) =
      -(rectanglePairWeight hs choice (fun c => c ∈ antiCells n)
        (fwSeedRectangle hseed (finProdFinEquiv (j,rect)), pair)) ^ 2 := by
  have h := fw_seed_rectangle_anti_orientation_eq_neg_weight hs hL choice
    (fwSeedRectangle hseed (finProdFinEquiv (j,rect))) pair
  have hh : physicalPairLineOrientation (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun c => c ∈ antiCells n)
        (j, prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect, pair)) =
      -rectanglePairWeight hs choice (fun c => c ∈ antiCells n)
        (fwSeedRectangle hseed (finProdFinEquiv (j,rect)), pair) := by
    unfold physicalPairLineOrientation
    rw [fw_seed_existing_rectangle_cell hseed hs choice sr sc hsr hsc j rect pair true,
      fw_seed_existing_rectangle_cell hseed hs choice sr sc hsr hsc j rect pair false]
    simpa [physicalPairLineOrientation] using h
  rw [hh, rectanglePairWeight_anti hs hL]
  split_ifs <;> norm_num

theorem fw_seed_actual_rectangle_anti_stage_orientation {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (j : Fin 16) :
    (∑ rect : Fin (4 * 6), ∑ pair : Fin 2,
      physicalPairLineOrientation (fwSeedExistingPairCells hseed hs
        (fwBridgeSeedRectangleChoice hrect hseed otherChoice) sr sc hsr hsc)
        (fun c => c ∈ antiCells n)
        (j, prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect, pair))) = -12 := by
  simp_rw [fw_seed_actual_rectangle_anti_orientation hseed hs hL]
  simp_rw [Finset.sum_neg_distrib]
  have h := fw_seed_offset_anti_stage_invoice hrect hseed hs hL otherChoice j
  change (∑ rect : Fin (4 * 6), ∑ pair : Fin 2,
    rectanglePairWeight hs (fwBridgeSeedRectangleChoice hrect hseed otherChoice)
      (fun c => c ∈ antiCells n) (fwSeedRectangle hseed (finProdFinEquiv (j,rect)),pair) ^ 2) = 12 at h
  rw [h]

theorem fw_seed_actual_rectangle_main_all_stages {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) :
    (∑ j : Fin 16, ∑ rect : Fin (4 * 6), ∑ pair : Fin 2,
      physicalPairLineOrientation (fwSeedExistingPairCells hseed hs
        (fwBridgeSeedRectangleChoice hrect hseed otherChoice) sr sc hsr hsc)
        (fun c => c ∈ mainCells n)
        (j, prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect, pair))) = -192 := by
  simp_rw [fw_seed_actual_rectangle_main_stage_orientation hrect hseed hs hL otherChoice sr sc hsr hsc]
  norm_num

theorem fw_seed_actual_rectangle_anti_all_stages {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) :
    (∑ j : Fin 16, ∑ rect : Fin (4 * 6), ∑ pair : Fin 2,
      physicalPairLineOrientation (fwSeedExistingPairCells hseed hs
        (fwBridgeSeedRectangleChoice hrect hseed otherChoice) sr sc hsr hsc)
        (fun c => c ∈ antiCells n)
        (j, prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect, pair))) = -192 := by
  simp_rw [fw_seed_actual_rectangle_anti_stage_orientation hrect hseed hs hL otherChoice sr sc hsr hsc]
  norm_num

theorem fw_seed_actual_seed_main_stage_orientation {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows sr)
    (packedCols : LayerPacking.PackedLayers reservedCols sc) (j : Fin 16) :
    (∑ q : Fin (6 * (n + 8)),
      physicalPairLineOrientation (fwSeedExistingPairCells hseed hs
        (fwBridgeSeedRectangleChoice hrect hseed otherChoice) sr sc hsr hsc)
        (fun c => c ∈ mainCells n) (j, q)) = -12 := by
  classical
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let hexact : (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega
  let e := Equiv.ofBijective (prefixStagePairSlot hfit hdiag)
    (prefixStagePairSlot_bijective hfit hdiag hexact)
  let choice := fwBridgeSeedRectangleChoice hrect hseed otherChoice
  let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
  let orient := fun q : Fin (6 * (n + 8)) => physicalPairLineOrientation cells (fun c => c ∈ mainCells n) (j, q)
  let weight := fun q : Fin (6 * (n + 8)) => physicalPairLineWeight cells (fun c => c ∈ mainCells n) (j, q)
  have hpoint (tag : PrefixStagePair 6 3 n) : orient (e tag) = -(weight (e tag)) ^ 2 := by
    cases tag with
    | inl x =>
      rcases x with ⟨rect, pair⟩
      change physicalPairLineOrientation cells (fun c => c ∈ mainCells n)
        (j, prefixDiagonalPairIndex hdiag (rect, pair)) =
        -(physicalPairLineWeight cells (fun c => c ∈ mainCells n)
        (j, prefixDiagonalPairIndex hdiag (rect, pair))) ^ 2
      rw [fw_seed_existing_rectangle_weight hseed hs hL choice sr sc hsr hsc]
      have h := fw_seed_actual_rectangle_main_orientation hseed hs hL choice sr sc hsr hsc j rect pair
      rw [rectanglePairWeight_main hs hL] at h
      exact h
    | inr x =>
      rcases x with ⟨network, k, edge⟩
      fin_cases network
      · have hf := (fw_seed_existing_row_off_diagonals hseed hs choice sr sc hsr hsc reservedRows packedRows j k edge false).1
        have ht := (fw_seed_existing_row_off_diagonals hseed hs choice sr sc hsr hsc reservedRows packedRows j k edge true).1
        change physicalPairLineOrientation cells (fun c => c ∈ mainCells n)
          (j, prefixOrdinaryPairIndex hfit (0, k, edge)) =
          -(physicalPairLineWeight cells (fun c => c ∈ mainCells n)
          (j, prefixOrdinaryPairIndex hfit (0, k, edge))) ^ 2
        unfold physicalPairLineOrientation physicalPairLineWeight
        rw [if_neg hf, if_neg ht]
        norm_num
      · have hf := (fw_seed_existing_column_off_diagonals hseed hs choice sr sc hsr hsc reservedCols packedCols j k edge false).1
        have ht := (fw_seed_existing_column_off_diagonals hseed hs choice sr sc hsr hsc reservedCols packedCols j k edge true).1
        change physicalPairLineOrientation cells (fun c => c ∈ mainCells n)
          (j, prefixOrdinaryPairIndex hfit (1, k, edge)) =
          -(physicalPairLineWeight cells (fun c => c ∈ mainCells n)
          (j, prefixOrdinaryPairIndex hfit (1, k, edge))) ^ 2
        unfold physicalPairLineOrientation physicalPairLineWeight
        rw [if_neg hf, if_neg ht]
        norm_num
  calc
    ∑ q, orient q = ∑ tag, orient (e tag) := (e.sum_comp orient).symm
    _ = ∑ tag, -(weight (e tag)) ^ 2 := by congr 1; funext tag; exact hpoint tag
    _ = -(∑ tag, (weight (e tag)) ^ 2) := Finset.sum_neg_distrib _
    _ = -(∑ q, (weight q) ^ 2) := congrArg Neg.neg (e.sum_comp (fun q => (weight q) ^ 2))
    _ = -12 := by rw [fw_seed_existing_main_squared_sum hrect hseed hs hL otherChoice sr sc hsr hsc reservedRows reservedCols packedRows packedCols j]

theorem fw_seed_actual_seed_anti_stage_orientation {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows sr)
    (packedCols : LayerPacking.PackedLayers reservedCols sc) (j : Fin 16) :
    (∑ q : Fin (6 * (n + 8)),
      physicalPairLineOrientation (fwSeedExistingPairCells hseed hs
        (fwBridgeSeedRectangleChoice hrect hseed otherChoice) sr sc hsr hsc)
        (fun c => c ∈ antiCells n) (j, q)) = -12 := by
  classical
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let hexact : (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega
  let e := Equiv.ofBijective (prefixStagePairSlot hfit hdiag)
    (prefixStagePairSlot_bijective hfit hdiag hexact)
  let choice := fwBridgeSeedRectangleChoice hrect hseed otherChoice
  let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
  let orient := fun q : Fin (6 * (n + 8)) => physicalPairLineOrientation cells (fun c => c ∈ antiCells n) (j, q)
  let weight := fun q : Fin (6 * (n + 8)) => physicalPairLineWeight cells (fun c => c ∈ antiCells n) (j, q)
  have hpoint (tag : PrefixStagePair 6 3 n) : orient (e tag) = -(weight (e tag)) ^ 2 := by
    cases tag with
    | inl x =>
      rcases x with ⟨rect, pair⟩
      change physicalPairLineOrientation cells (fun c => c ∈ antiCells n)
        (j, prefixDiagonalPairIndex hdiag (rect, pair)) =
        -(physicalPairLineWeight cells (fun c => c ∈ antiCells n)
        (j, prefixDiagonalPairIndex hdiag (rect, pair))) ^ 2
      rw [fw_seed_existing_rectangle_anti_weight hseed hs hL choice sr sc hsr hsc]
      have h := fw_seed_actual_rectangle_anti_orientation hseed hs hL choice sr sc hsr hsc j rect pair
      rw [rectanglePairWeight_anti hs hL] at h
      exact h
    | inr x =>
      rcases x with ⟨network, k, edge⟩
      fin_cases network
      · have hf := (fw_seed_existing_row_off_diagonals hseed hs choice sr sc hsr hsc reservedRows packedRows j k edge false).2
        have ht := (fw_seed_existing_row_off_diagonals hseed hs choice sr sc hsr hsc reservedRows packedRows j k edge true).2
        change physicalPairLineOrientation cells (fun c => c ∈ antiCells n)
          (j, prefixOrdinaryPairIndex hfit (0, k, edge)) =
          -(physicalPairLineWeight cells (fun c => c ∈ antiCells n)
          (j, prefixOrdinaryPairIndex hfit (0, k, edge))) ^ 2
        unfold physicalPairLineOrientation physicalPairLineWeight
        rw [if_neg hf, if_neg ht]
        norm_num
      · have hf := (fw_seed_existing_column_off_diagonals hseed hs choice sr sc hsr hsc reservedCols packedCols j k edge false).2
        have ht := (fw_seed_existing_column_off_diagonals hseed hs choice sr sc hsr hsc reservedCols packedCols j k edge true).2
        change physicalPairLineOrientation cells (fun c => c ∈ antiCells n)
          (j, prefixOrdinaryPairIndex hfit (1, k, edge)) =
          -(physicalPairLineWeight cells (fun c => c ∈ antiCells n)
          (j, prefixOrdinaryPairIndex hfit (1, k, edge))) ^ 2
        unfold physicalPairLineOrientation physicalPairLineWeight
        rw [if_neg hf, if_neg ht]
        norm_num
  calc
    ∑ q, orient q = ∑ tag, orient (e tag) := (e.sum_comp orient).symm
    _ = ∑ tag, -(weight (e tag)) ^ 2 := by congr 1; funext tag; exact hpoint tag
    _ = -(∑ tag, (weight (e tag)) ^ 2) := Finset.sum_neg_distrib _
    _ = -(∑ q, (weight q) ^ 2) := congrArg Neg.neg (e.sum_comp (fun q => (weight q) ^ 2))
    _ = -12 := by rw [fw_seed_existing_anti_squared_sum hrect hseed hs hL otherChoice sr sc hsr hsc reservedRows reservedCols packedRows packedCols j]

theorem fw_seed_actual_seed_main_all_stage_orientation {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows sr)
    (packedCols : LayerPacking.PackedLayers reservedCols sc) :
    (∑ j : Fin 16, ∑ q : Fin (6 * (n + 8)),
      physicalPairLineOrientation (fwSeedExistingPairCells hseed hs
        (fwBridgeSeedRectangleChoice hrect hseed otherChoice) sr sc hsr hsc)
        (fun c => c ∈ mainCells n) (j,q)) = -192 := by
  simp_rw [fw_seed_actual_seed_main_stage_orientation hrect hseed hs hL otherChoice sr sc hsr hsc reservedRows reservedCols packedRows packedCols]
  norm_num

theorem fw_seed_actual_seed_anti_all_stage_orientation {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows sr)
    (packedCols : LayerPacking.PackedLayers reservedCols sc) :
    (∑ j : Fin 16, ∑ q : Fin (6 * (n + 8)),
      physicalPairLineOrientation (fwSeedExistingPairCells hseed hs
        (fwBridgeSeedRectangleChoice hrect hseed otherChoice) sr sc hsr hsc)
        (fun c => c ∈ antiCells n) (j,q)) = -192 := by
  simp_rw [fw_seed_actual_seed_anti_stage_orientation hrect hseed hs hL otherChoice sr sc hsr hsc reservedRows reservedCols packedRows packedCols]
  norm_num

end
end Sude
