import Sude.FWPhysicalDoubleBlockCells
import Sude.DoubleBlockProtectedLogReallocation
import Sude.FWGrowthOrdinaryRecenterLineBound

/-! Specialize the supplied theta-witness bridge/wide all-line scores to
actual physical rows and columns, with the same source and ordered squares.
No square, score, full-line or later-flow existence is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

/-- The strict all-line midpoint scores yield the weak row and column bounds
needed by the same-witness four-family assembly. -/
theorem fw_theta_bridge_wide_line_scores {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc wr wc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (source ordered : Cell n ≃ Fin (n*n)) (B W : ℝ)
    (hB : ∀ l : Fin ((n+n)+2),
      |doubleBlockActualCenteredScore (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
        (fun z => z ∈ physicalAllLineCells l) source ordered| < B)
    (hW : ∀ l : Fin ((n+n)+2),
      |doubleBlockActualCenteredScore (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
        (fun z => z ∈ physicalAllLineCells l) source ordered| < W) :
    (∀ r : Fin n, |doubleBlockActualCenteredScore (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
      (fun z => z ∈ rowCells r) source ordered| ≤ B) ∧
    (∀ r : Fin n, |doubleBlockActualCenteredScore (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
      (fun z => z ∈ rowCells r) source ordered| ≤ W) ∧
    (∀ c : Fin n, |doubleBlockActualCenteredScore (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)
      (fun z => z ∈ columnCells c) source ordered| ≤ B) ∧
    (∀ c : Fin n, |doubleBlockActualCenteredScore (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
      (fun z => z ∈ columnCells c) source ordered| ≤ W) := by
  classical
  constructor
  · intro r
    exact le_of_lt (by simpa only [fwGrowthRowLineLabel, physicalAllLineCells, Equiv.symm_apply_apply] using hB (fwGrowthRowLineLabel r))
  constructor
  · intro r
    exact le_of_lt (by simpa only [fwGrowthRowLineLabel, physicalAllLineCells, Equiv.symm_apply_apply] using hW (fwGrowthRowLineLabel r))
  constructor
  · intro c
    exact le_of_lt (by simpa only [fwGrowthColumnLineLabel, physicalAllLineCells, Equiv.symm_apply_apply] using hB (fwGrowthColumnLineLabel c))
  · intro c
    exact le_of_lt (by simpa only [fwGrowthColumnLineLabel, physicalAllLineCells, Equiv.symm_apply_apply] using hW (fwGrowthColumnLineLabel c))

end
end Sude
