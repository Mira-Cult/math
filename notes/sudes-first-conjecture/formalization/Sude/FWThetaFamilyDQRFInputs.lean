import Sude.FWThetaFamilyWitness
import Sude.FWFirstBandDQRFInputs
import Sude.FWPostDiagonalCompletionGeometry
import Sude.FWFullReservationQuarterCapacity

/-! Derive the geometric DQ/RF premises from one supplied four-family witness.
The widened interval, deletion budget, numerical gate and oddness remain
explicit inputs for the same ordered square and its full reservation. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Full physical reservation, including spare rectangle capacity, on the
geometry carried by the supplied family witness. -/
def fwThetaFamilyFull {n : ℕ} {choice : Fin (fwJointRectangleCount n 254) → Bool}
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice) : Finset (Cell n) :=
  packedRectangleSupport f.hs choice ∪ LayerPacking.layersSupport (((f.br ++ f.sr) ++ f.wr) ++ f.gr) ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport (((f.bc ++ f.sc) ++ f.wc) ++ f.gc))

/-- The existing packed geometry supplies center avoidance, quarter capacity,
and the post-diagonal row and column load bounds for arbitrary `bits`. The
separate load inequality and all widened-interval analytic premises are
retained, with natural-number arithmetic performed before casting. -/
theorem fw_theta_family_dqrf_inputs
    {n bits Dold : ℕ} (hnlo : 19485 ≤ n)
    {choice : Fin (fwJointRectangleCount n 254) → Bool}
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice)
    (ε : ℝ) (hε : 0 ≤ ε) (hodd : Odd n)
    (hload : 4 * (12 * (5 + 16 + 3 * (n / 450) + f.stages.length) + 6 * bits + 4) ≤ n)
    (hleft : 1 ≤ centralEntriesMean (actualUnusedPool f.ordered (fwThetaFamilyFull f)) centralPoolValue -
      ε * poolMaximum n - 3 * (poolMaximum n : ℝ) / (4*n))
    (hright : centralEntriesMean (actualUnusedPool f.ordered (fwThetaFamilyFull f)) centralPoolValue +
      ε * poolMaximum n + 3 * (poolMaximum n : ℝ) / (4*n) ≤ poolMaximum n)
    (hdeleted : (apInterval
      (centralEntriesMean (actualUnusedPool f.ordered (fwThetaFamilyFull f)) centralPoolValue -
        ε * poolMaximum n - 3 * (poolMaximum n : ℝ) / (4*n))
      (centralEntriesMean (actualUnusedPool f.ordered (fwThetaFamilyFull f)) centralPoolValue +
        ε * poolMaximum n + 3 * (poolMaximum n : ℝ) / (4*n)) 2 1 ∩
        (fwThetaFamilyFull f).image (entry f.ordered)).card ≤ Dold)
    (hgate : (((9 * bits + 6) * n : ℕ) : ℝ) ≤
      (2 * (ε * poolMaximum n) - (1036 / 125 : ℝ) * Real.sqrt (poolMaximum n)) /
        Real.log (poolMaximum n) - (((Dold + (2*n - 1) : ℕ)) : ℝ)) :
    FWFirstBandDQRFInputs n f.stages.length bits Dold (by omega) ε f.ordered (fwThetaFamilyFull f) := by
  classical
  have hocc := fw_post_diagonal_completion_geometry f.hs choice f.br f.sr f.wr f.gr f.bc f.sc f.wc f.gc
    f.hbr f.hsr f.hwr f.hgr f.hbc f.hsc f.hwc f.hgc f.hrows f.hcols
  dsimp only at hocc
  have hcapacity := fw_full_reservation_quarter_capacity hnlo f.stageCap
    f.hrect f.hseedrect f.hwide f.hoff f.hs choice f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc
    f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc f.hrows f.hcols
  dsimp only at hcapacity
  refine ⟨hε, hodd, ?_, ?_, hload, ?_, ?_, ?_, ?_, hleft, hright, hdeleted, hgate⟩
  · simpa only [fwThetaFamilyFull] using
      fw_full_keepout_avoids_center f.hs (by omega) choice _ _ f.hrows f.hcols
  · simpa only [fwThetaFamilyFull] using hcapacity
  · intro i
    simpa only [fwThetaFamilyFull] using (hocc.2.2.1 i).1
  · intro i
    have h := (hocc.2.2.1 i).2
    dsimp only [fwThetaFamilyFull]
    omega
  · intro i
    simpa only [fwThetaFamilyFull] using (hocc.2.2.2 i).1
  · intro i
    have h := (hocc.2.2.2 i).2
    dsimp only [fwThetaFamilyFull]
    omega

end
end Sude
