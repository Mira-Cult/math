import Sude.FWSeedSignedDiagonalScore
import Sude.FWSeedDiagonalWeightSum
import Sude.FWSeedDiagonalOrientation
import Sude.LayerPackingSegments

/-! The supplied seed family with the prescribed 12/12 diagonal choice has
equal diagonal invoices. All geometry comes from this same family. -/
namespace Sude
noncomputable section
open scoped BigOperators
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

theorem fw_seed_prescribed_diagonal_difference {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (f : FWThetaFamilyWitness n L (fwBridgeSeedRectangleChoice hrect hseed otherChoice)) :
    let seed := fwSeedExistingPairCells f.hseedrect f.hs
      (fwBridgeSeedRectangleChoice hrect hseed otherChoice) f.sr f.sc f.hsr f.hsc
    |(∑ z ∈ (Finset.univ.image seed).filter (fun z => z ∈ mainCells n), (entry f.ordered z : ℝ)) -
     (∑ z ∈ (Finset.univ.image seed).filter (fun z => z ∈ antiCells n), (entry f.ordered z : ℝ))| ≤
      2 * Real.sqrt (((11/2 : ℝ)*((2^30 : ℕ) : ℝ)^2)*Real.log (4 * (((n+n)+2 : ℕ) : ℝ))/2) := by
  classical
  let reservedRows := packedRectangleSupport f.hs (fwBridgeSeedRectangleChoice hrect hseed otherChoice)
  let reservedCols := LayerPacking.transposeCells
    (reservedRows ∪ LayerPacking.layersSupport (((f.br ++ f.sr) ++ f.wr) ++ f.gr))
  have packedRows : LayerPacking.PackedLayers reservedRows f.sr :=
    (f.hrows.prefix ((f.br ++ f.sr) ++ f.wr) f.gr).segment f.br f.sr f.wr
  have packedCols : LayerPacking.PackedLayers reservedCols f.sc :=
    (f.hcols.prefix ((f.bc ++ f.sc) ++ f.wc) f.gc).segment f.bc f.sc f.wc
  apply fw_seed_signed_diagonal_of_equal_invoices f
  · intro j
    rw [fw_seed_existing_main_weight_sum hrect f.hseedrect f.hs hL otherChoice f.sr f.sc
      f.hsr f.hsc reservedRows reservedCols packedRows packedCols j,
      fw_seed_existing_anti_weight_sum hrect f.hseedrect f.hs hL otherChoice f.sr f.sc
      f.hsr f.hsc reservedRows reservedCols packedRows packedCols j]
  · have hm := fw_seed_actual_seed_main_all_stage_orientation hrect f.hseedrect f.hs hL otherChoice
      f.sr f.sc f.hsr f.hsc reservedRows reservedCols packedRows packedCols
    have ha := fw_seed_actual_seed_anti_all_stage_orientation hrect f.hseedrect f.hs hL otherChoice
      f.sr f.sc f.hsr f.hsc reservedRows reservedCols packedRows packedCols
    simpa only [Fintype.sum_prod_type] using hm.trans ha.symm

theorem fw_seed_prescribed_first_band_diagonal_difference {n L : ℕ}
    (lower : RSIndexLower) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (f : FWThetaFamilyWitness n L (fwBridgeSeedRectangleChoice hrect hseed otherChoice)) :
    let seed := fwSeedExistingPairCells f.hseedrect f.hs
      (fwBridgeSeedRectangleChoice hrect hseed otherChoice) f.sr f.sc f.hsr f.hsc
    |(∑ z ∈ (Finset.univ.image seed).filter (fun z => z ∈ mainCells n), (entry f.ordered z : ℝ)) -
     (∑ z ∈ (Finset.univ.image seed).filter (fun z => z ∈ antiCells n), (entry f.ordered z : ℝ))| ≤
      3 * (poolMaximum n : ℝ) := by
  exact (fw_seed_prescribed_diagonal_difference hrect hseed hL otherChoice f).trans
    (fw_first_band_twice_seed_radius_le_three_pool lower hnlo hnhi)

end
end Sude
