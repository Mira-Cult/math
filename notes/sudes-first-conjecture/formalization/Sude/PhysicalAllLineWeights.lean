import Sude.PrefixDiagonalSlotWeights
import Sude.PhysicalAllLineProbability

/-! Identify every labelled probability weight with actual physical line incidence. -/
namespace Sude
noncomputable section

/-- The labelled row, column, main, or antidiagonal cell set. Labels remain
separate even when their cell sets coincide. -/
def physicalAllLineCells {n : ℕ} (l : Fin ((n + n) + 2)) : Finset (Cell n) :=
  match (finSumFinEquiv (m := n + n) (n := 2)).symm l with
  | Sum.inl rc =>
      match (finSumFinEquiv (m := n) (n := n)).symm rc with
      | Sum.inl r => rowCells r
      | Sum.inr c => columnCells c
  | Sum.inr diag => if diag = 0 then mainCells n else antiCells n

/-- For every allocator slot, the all-line probability weight is exactly
the number of its two actual cells belonging to the corresponding labelled
line. Exact capacity and the injective slot map are both used. -/
theorem physicalAllLineWeight_eq_pair_incidence {P d layers n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (otherChoice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows rows)
    (packedCols : LayerPacking.PackedLayers reservedCols cols)
    (l : Fin ((n + n) + 2)) (j : Fin P) (q : Fin Q) :
    physicalPairLineWeight
      (prefixPairCells hfit hdiag hexact hrect hs (bridgeDiagonalChoice hrect otherChoice) rows cols hrows hcols)
      (fun c => c ∈ physicalAllLineCells l) (j, q) =
    physicalAllLineWeights hfit hdiag hrect hs otherChoice rows cols hrows hcols l j q := by
  obtain ⟨tag, rfl⟩ := (prefixStagePairSlot_bijective hfit hdiag hexact).2 q
  cases hl : (finSumFinEquiv (m := n + n) (n := 2)).symm l with
  | inl rc =>
    cases hrc : (finSumFinEquiv (m := n) (n := n)).symm rc with
    | inl r =>
      have hp := prefixPairCells_row_weight_at_label hfit hdiag hexact hrect hs
        (bridgeDiagonalChoice hrect otherChoice) rows cols hrows hcols j r tag
      have hw := liftedSlotWeight_at (prefixStagePairSlot hfit hdiag)
        (prefixStagePairSlot_injective hfit hdiag)
        (prefixStageRowIncidence hrect hs (bridgeDiagonalChoice hrect otherChoice) rows cols hrows hcols j r) tag
      change physicalRowSlotWeight hfit hdiag hrect hs (bridgeDiagonalChoice hrect otherChoice)
        rows cols hrows hcols j r (prefixStagePairSlot hfit hdiag tag) = _ at hw
      simpa only [physicalAllLineCells, physicalAllLineWeights, physicalRowColumnWeights, hl, hrc] using hp.trans hw.symm
    | inr c =>
      have hp := prefixPairCells_column_weight_at_label hfit hdiag hexact hrect hs
        (bridgeDiagonalChoice hrect otherChoice) rows cols hrows hcols j c tag
      have hw := liftedSlotWeight_at (prefixStagePairSlot hfit hdiag)
        (prefixStagePairSlot_injective hfit hdiag)
        (prefixStageColumnIncidence hrect hs (bridgeDiagonalChoice hrect otherChoice) rows cols hrows hcols j c) tag
      change physicalColumnSlotWeight hfit hdiag hrect hs (bridgeDiagonalChoice hrect otherChoice)
        rows cols hrows hcols j c (prefixStagePairSlot hfit hdiag tag) = _ at hw
      simpa only [physicalAllLineCells, physicalAllLineWeights, physicalRowColumnWeights, hl, hrc] using hp.trans hw.symm
  | inr diag =>
    by_cases hzero : diag = 0
    · have hp := prefixPairCells_main_weight_at_label hfit hdiag hexact hrect hs
        (bridgeDiagonalChoice hrect otherChoice) rows cols hrows hcols reservedRows reservedCols packedRows packedCols j tag
      have hw := liftedSlotWeight_at (prefixStagePairSlot hfit hdiag)
        (prefixStagePairSlot_injective hfit hdiag)
        (prefixStageDiagonalIncidence hrect hs (bridgeDiagonalChoice hrect otherChoice) (fun c => c ∈ mainCells n) j) tag
      change physicalDiagonalSlotWeight hfit hdiag hrect hs (bridgeDiagonalChoice hrect otherChoice)
        (fun c => c ∈ mainCells n) j (prefixStagePairSlot hfit hdiag tag) = _ at hw
      simpa only [physicalAllLineCells, physicalAllLineWeights, hl, hzero, if_true] using hp.trans hw.symm
    · have hp := prefixPairCells_anti_weight_at_label hfit hdiag hexact hrect hs
        (bridgeDiagonalChoice hrect otherChoice) rows cols hrows hcols reservedRows reservedCols packedRows packedCols j tag
      have hw := liftedSlotWeight_at (prefixStagePairSlot hfit hdiag)
        (prefixStagePairSlot_injective hfit hdiag)
        (prefixStageDiagonalIncidence hrect hs (bridgeDiagonalChoice hrect otherChoice) (fun c => c ∈ antiCells n) j) tag
      change physicalDiagonalSlotWeight hfit hdiag hrect hs (bridgeDiagonalChoice hrect otherChoice)
        (fun c => c ∈ antiCells n) j (prefixStagePairSlot hfit hdiag tag) = _ at hw
      simpa only [physicalAllLineCells, physicalAllLineWeights, hl, hzero, if_false] using hp.trans hw.symm

end
end Sude
