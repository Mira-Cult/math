import Sude.FWProjectedFullClassifiedCover
import Sude.CYDiagonalBandCompletion
import Sude.FWFullReservationQuarterCapacity
import Sude.FWPostDiagonalCompletionGeometry
import Sude.FWFirstBandFrozenCYStockGate
import Sude.FWFirstBandFrozenCYEndpoints
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Frozen-width CY completion for the supplied projected family and its
actual network reference. Final target and flow bounds are separate. -/
theorem fw_projected_frozen_cy_completion
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hodd : Odd n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice)
    (p : Fin 3 → Equiv.Perm (Fin n)) (oldReference : Cell n ≃ Fin (n*n))
    (roles : Finset (Cell n))
    (net : FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs choice
      f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
      f.hrows f.hcols p f.ordered oldReference roles) :
    let full := fwThetaFamilyFull f
    let final := full ∪ unreservedDiagonalCells full
    ∃ b c : Cell n ≃ Fin (n*n),
      (∀ z ∈ full, entry b z = entry oldReference z) ∧
      (∀ z ∈ final, entry c z = entry b z) ∧
      (∀ z ∈ full, entry c z = entry oldReference z) ∧
      |(mainSum c : ℝ) - ((∑ z ∈ mainCells n ∩ full, (entry oldReference z : ℝ)) +
        ((mainCells n \ full).card : ℝ)*centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| ≤ (poolMaximum n : ℝ) ∧
      |(antiSum c : ℝ) - ((∑ z ∈ antiCells n ∩ full, (entry oldReference z : ℝ)) +
        ((antiCells n \ full).card : ℝ)*centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| ≤ (3/2 : ℝ)*poolMaximum n ∧
      (∀ i, |(rowSum c i : ℝ) - ((∑ z ∈ rowCells i ∩ full, (entry oldReference z : ℝ)) +
        ((rowCells i \ full).card : ℝ)*centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| <
        (4+(7+1/(n : ℝ))*(4262317/50000000 : ℝ))*poolMaximum n) ∧
      (∀ i, |(columnSum c i : ℝ) - ((∑ z ∈ columnCells i ∩ full, (entry oldReference z : ℝ)) +
        ((columnCells i \ full).card : ℝ)*centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue)| <
        (4+(7+1/(n : ℝ))*(4262317/50000000 : ℝ))*poolMaximum n) ∧
      mainSum c = mainSum b ∧ antiSum c = antiSum b ∧
      Set.range (entry c) = pool n ∧ Function.Injective (entry c) := by
  classical
  let rows := (((f.br++f.sr)++f.wr)++f.gr)
  let cols := (((f.bc++f.sc)++f.wc)++f.gc)
  let full := fwThetaFamilyFull f
  let wide := Finset.univ.image (fwWidePhysicalCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc)
  let accounted := (full \ wide).image (entry f.ordered)
  let shielded := doubleBatchLow f.blocks ∪ doubleBatchHigh f.blocks
  let m : ℝ := (Lucas.poolTotal n : ℝ)/(n*n : ℕ)
  let Dold := 12*(n+8)*5+12*(n+8)*254
  have hm := (fw_projected_reference_unused_mean_sigma11 bmor lower upper hnlo hnhi choice f p oldReference roles net).2.2.2.2
  have hmean : |centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue - m| ≤
      (11/100 : ℝ)*poolMaximum n := by
    simpa only [full, m, prescribedPoolValues_mean] using hm
  have hc := fw_projected_full_classified_cover bmor lower upper hnlo hnhi choice f p oldReference roles net
  have hcover : full.image (entry oldReference) ⊆ accounted ∪ shielded := hc.1
  have haccount : accounted.card ≤ Dold := by
    have hh := hc.2.1
    dsimp only [Dold]
    convert hh using 1; ring
  have hband : ∀ v ∈ shielded, (v : ℝ) ≤ m - (poolMaximum n : ℝ)/4 + 0*poolMaximum n ∨
      m + (poolMaximum n : ℝ)/4 - 0*poolMaximum n ≤ v := by
    simpa only [zero_mul, add_zero, sub_zero] using hc.2.2
  have hreserve := fw_full_reservation_quarter_capacity hnlo f.stageCap f.hrect f.hseedrect f.hwide f.hoff f.hs choice
    f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc f.hrows f.hcols
  have hloadbase := fw_first_band_post_diagonal_load hnlo hnhi f.stageCap
  have hload : 4*(2*(rows.length+cols.length)+4) ≤ n := by
    dsimp [rows, cols]
    simp only [List.length_append, f.hbr,f.hbc,f.hsr,f.hsc,f.hwr,f.hwc,f.hgr,f.hgc]
    omega
  have he := fw_first_band_frozen_cy_endpoints bmor lower upper hnlo hnhi
  dsimp only at he
  have hgap : (11/100 : ℝ)+(4262317/50000000 : ℝ)+3/(4*(n : ℝ))+0 < 1/4 := by linarith [he.1]
  have hgate := fw_first_band_frozen_cy_stock_gate bmor lower upper hnlo hnhi
  have hresult := cy_dq_sharp_completion_from_mean_and_bands bmor upper f.hs
    (by simp [fwJointRectangleCount]; omega) (by omega) (by omega) hodd choice rows cols f.hrows f.hcols hload
    oldReference accounted shielded m (11/100 : ℝ) (4262317/50000000 : ℝ) 0 Dold
    (by norm_num) hreserve hmean hgap he.2.1 he.2.2 hcover haccount hband hgate
  simpa only [rows, cols, full, fwThetaFamilyFull] using hresult
end
end Sude

