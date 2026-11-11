import Sude.BTGrowingPhysicalStageTotals
import Sude.RectangleDiagonalIncidence
import Sude.FWGrowthRectangleChoice
import Sude.FWGrowthDiagonalSlots
import Sude.DiagonalPhysicalInvoice

/-! Physical interpretation of selected growth rectangle pair slots. -/
namespace Sude
noncomputable section

/-- A growth rectangle pair index names its actual offset rectangle corners. -/
theorem fw_growth_offset_rectangle_cell {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = P * 3)
    (hc : cols.length = P * 3) (j : Fin P) (rect : Fin (4 * 6))
    (pair : Fin 2) (side : Bool) :
    btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
      ((j, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (rect,pair)), side) =
    packedRectangleCorner hs choice
      (btGrowingOffsetRectangle offset hoff (finProdFinEquiv (j,rect)), prefixPairCorner pair side) := by
  let hfit : (4*6)*2 + 2*(3*n) ≤ 6*(n+8) := by omega
  let hdiag : (4*6)*2 ≤ 6*(n+8) := by omega
  let heq : (4*6)*2 + 2*(3*n) = 6*(n+8) := by omega
  let e := prefixPhysicalInputEquiv (P := P) hfit hdiag heq
  have he : e.symm ((j, prefixDiagonalPairIndex hdiag (rect,pair)), side) =
      Sum.inl (finProdFinEquiv (j,rect), prefixPairCorner pair side) := by
    apply e.symm_apply_eq.mpr
    simpa [e, prefixPhysicalInputEquiv, prefixPhysicalInput] using
      (prefixRectangleInput_pair hdiag j rect pair side).symm
  change btGrowingOffsetCells offset hoff hs choice rows cols hr hc
    (e.symm ((j, prefixDiagonalPairIndex hdiag (rect,pair)), side)) = _
  rw [he]
  rfl

/-- The balanced choice gives the exact physical diagonal pair weights:
first pairs in the first twelve rectangles meet the main diagonal, first
pairs in the last twelve meet the antidiagonal, all partners meet neither. -/
theorem fw_growth_balanced_rectangle_weights {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = P * 3)
    (hc : cols.length = P * 3) (j : Fin P)
    (hchoice : ∀ rect : Fin (4*6),
      choice (btGrowingOffsetRectangle offset hoff (finProdFinEquiv (j,rect))) = decide (rect.val < 12))
    (rect : Fin (4*6)) (pair : Fin 2) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    let idx := (j, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (rect,pair))
    physicalPairLineWeight cells (fun c => c ∈ mainCells n) idx =
      (if pair = 0 ∧ rect.val < 12 then 1 else 0) ∧
    physicalPairLineWeight cells (fun c => c ∈ antiCells n) idx =
      (if pair = 0 ∧ ¬ rect.val < 12 then 1 else 0) := by
  classical
  dsimp only
  have hm := rectanglePairWeight_main hs hL choice
    (btGrowingOffsetRectangle offset hoff (finProdFinEquiv (j,rect))) pair
  have ha := rectanglePairWeight_anti hs hL choice
    (btGrowingOffsetRectangle offset hoff (finProdFinEquiv (j,rect))) pair
  unfold physicalPairLineWeight
  rw [fw_growth_offset_rectangle_cell offset hoff hs choice rows cols hr hc j rect pair false,
    fw_growth_offset_rectangle_cell offset hoff hs choice rows cols hr hc j rect pair true]
  rw [hchoice rect] at hm ha
  constructor
  · simpa [rectanglePairWeight] using hm
  · simpa [rectanglePairWeight] using ha

/-- The previously reserved maximum-stage FW choice supplies the balanced
choice for each actually realized growth stage, without identifying the
full maximum-stage and realized-stage choice functions. -/
theorem fw_growth_reserved_choice_rectangle_weights {P M n L : ℕ}
    (hrect : 5*(4*6) ≤ L) (hseed : 5*(4*6)+16*(4*6) ≤ L)
    (hwide : 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6) ≤ L)
    (hmax : 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)+M*(4*6) ≤ L)
    (hoff : 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)+P*(4*6) ≤ L)
    (hle : P ≤ M) (hs : 2*L+1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = P*3)
    (hc : cols.length = P*3) (j : Fin P) (rect : Fin (4*6)) (pair : Fin 2) :
    let offset := 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)
    let choice := fwBridgeSeedWideGrowthChoice hrect hseed hwide hmax otherChoice
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    let idx := (j, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (rect,pair))
    physicalPairLineWeight cells (fun c => c ∈ mainCells n) idx =
      (if pair = 0 ∧ rect.val < 12 then 1 else 0) ∧
    physicalPairLineWeight cells (fun c => c ∈ antiCells n) idx =
      (if pair = 0 ∧ ¬ rect.val < 12 then 1 else 0) := by
  dsimp only
  apply fw_growth_balanced_rectangle_weights _ hoff hs hL _ rows cols hr hc j
  intro i
  simpa using fwBridgeSeedWideGrowthChoice_offset_restrict hrect hseed hwide hmax hoff hle otherChoice j i

/-- Every ordinary growth slot avoids both diagonals when its own layer is
packed; this is independent of the rectangle-choice split. -/
theorem fw_growth_ordinary_off_diagonals {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P*3) (hc : cols.length = P*3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows rows)
    (hcols : LayerPacking.PackedLayers reservedCols cols)
    (j : Fin P) (tag : Fin 2) (k : Fin 3) (edge : Fin n) (side : Bool) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    let cell := cells ((j, prefixOrdinaryPairIndex
      (show (4*6)*2+2*(3*n) ≤ 6*(n+8) by omega) (tag,k,edge)),side)
    cell ∉ mainCells n ∧ cell ∉ antiCells n := by
  let hfit : (4*6)*2+2*(3*n) ≤ 6*(n+8) := by omega
  let hdiag : (4*6)*2 ≤ 6*(n+8) := by omega
  let heq : (4*6)*2+2*(3*n) = 6*(n+8) := by omega
  let e := prefixPhysicalInputEquiv (P := P) hfit hdiag heq
  fin_cases tag
  · have he : e.symm ((j, prefixOrdinaryPairIndex hfit (0,k,edge)),side) =
        Sum.inr (Sum.inl (finProdFinEquiv (j,k),(edge,side))) := by
      apply e.symm_apply_eq.mpr
      simpa [e, prefixPhysicalInputEquiv, prefixPhysicalInput] using
        (prefixStageLayer_networkInput hfit rfl 0 j k edge side).symm
    have hcell : btGrowingOffsetPairCells hfit hdiag heq offset hoff hs choice rows cols hr hc
        ((j, prefixOrdinaryPairIndex hfit (0,k,edge)),side) =
        LayerPacking.layerCell (prefixStageLayer rows hr j k).1
          (prefixStageLayer rows hr j k).2 (edge,side) := by
      change btGrowingOffsetCells offset hoff hs choice rows cols hr hc
        (e.symm ((j, prefixOrdinaryPairIndex hfit (0,k,edge)),side)) = _
      rw [he]
      exact prefixStageLayer_sequenceCell rows hr j k edge side
    change btGrowingOffsetPairCells hfit hdiag heq offset hoff hs choice rows cols hr hc
        ((j, prefixOrdinaryPairIndex hfit (0,k,edge)),side) ∉ mainCells n ∧
      btGrowingOffsetPairCells hfit hdiag heq offset hoff hs choice rows cols hr hc
        ((j, prefixOrdinaryPairIndex hfit (0,k,edge)),side) ∉ antiCells n
    rw [hcell]
    exact prefixStageLayer_off_diagonals rows hr reservedRows hrows j k edge side
  · have he : e.symm ((j, prefixOrdinaryPairIndex hfit (1,k,edge)),side) =
        Sum.inr (Sum.inr (finProdFinEquiv (j,k),(edge,side))) := by
      apply e.symm_apply_eq.mpr
      simpa [e, prefixPhysicalInputEquiv, prefixPhysicalInput] using
        (prefixStageLayer_networkInput hfit rfl 1 j k edge side).symm
    have hcell : btGrowingOffsetPairCells hfit hdiag heq offset hoff hs choice rows cols hr hc
        ((j, prefixOrdinaryPairIndex hfit (1,k,edge)),side) =
        (LayerPacking.layerCell (prefixStageLayer cols hc j k).1
          (prefixStageLayer cols hc j k).2 (edge,side)).swap := by
      change btGrowingOffsetCells offset hoff hs choice rows cols hr hc
        (e.symm ((j, prefixOrdinaryPairIndex hfit (1,k,edge)),side)) = _
      rw [he]
      exact congrArg Prod.swap (prefixStageLayer_sequenceCell cols hc j k edge side)
    change btGrowingOffsetPairCells hfit hdiag heq offset hoff hs choice rows cols hr hc
        ((j, prefixOrdinaryPairIndex hfit (1,k,edge)),side) ∉ mainCells n ∧
      btGrowingOffsetPairCells hfit hdiag heq offset hoff hs choice rows cols hr hc
        ((j, prefixOrdinaryPairIndex hfit (1,k,edge)),side) ∉ antiCells n
    rw [hcell]
    exact prefixStageLayer_swap_off_diagonals cols hc reservedCols hcols j k edge side

end
end Sude
