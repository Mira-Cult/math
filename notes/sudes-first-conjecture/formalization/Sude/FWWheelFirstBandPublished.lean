import Sude.FWActualIndexRatio
import Sude.FWWheelFirstBandFW3

/-! First-band actual-Q/X WW4 quota using the explicit finite q=4 prime-count
and RS index hypotheses. The V envelope remains a hypothesis. -/
namespace Sude
noncomputable section

/-- The FW3 log and index-ratio hypotheses in the first-band WW4 quota follow
from the supplied finite q=4 prime-count and RS lower/upper hypotheses. The
rate is the actual Q/X, not the frozen source's band-majorant charge. -/
theorem fw_wheel_ww4_first_band_quota_from_imports
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} {V : ℝ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (hVpos : 0 < V) (hV : V ≤ 231 / 10) :
    2 * (23 / 48 - 3981035 / 10000000 : ℝ) *
      (((9999 / 10000 : ℝ) * (7525444 / 10000000)) / V)^2 ≥
    2 * 6 * (((6 * (n + 8) : ℕ) : ℝ) / poolMaximum n) := by
  exact fw_wheel_ww4_first_band_quota_of_fw3 hnlo
    (fw_poolMaximum_log_gt_181_eighths lower hnlo)
    (fw_actual_index_ratio bmor lower upper hnlo (by omega)) hVpos hV

end
end Sude
