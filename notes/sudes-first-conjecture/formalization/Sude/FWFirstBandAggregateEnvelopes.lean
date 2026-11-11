import Sude.FWThetaMeanFromAggregate
import Sude.FWWheelFirstBandPointwise

/-! First-band WW4 quota and stock envelopes from explicitly supplied
aggregate odd-prime count error. No theta-to-count theorem is asserted. -/
namespace Sude
noncomputable section

/-- The actual first-band WW4 quota from the aggregate count input and
existing RS hypotheses, with the V envelope still explicitly supplied. -/
theorem fw_wheel_ww4_first_band_quota_of_aggregate
    (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} {V : ℝ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (hcount : OddPrimeCountUniformBound (poolMaximum n : ℝ)
      ((1367 / 250 : ℝ) * (Real.sqrt (poolMaximum n : ℝ) /
        Real.log (poolMaximum n : ℝ))))
    (hVpos : 0 < V) (hV : V ≤ 231 / 10) :
    2 * (23 / 48 - 3981035 / 10000000 : ℝ) *
      (((9999 / 10000 : ℝ) * (7525444 / 10000000)) / V)^2 ≥
    2 * 6 * (((6 * (n + 8) : ℕ) : ℝ) / poolMaximum n) := by
  exact fw_wheel_ww4_first_band_quota_of_fw3 hnlo
    (fw_poolMaximum_log_gt_181_eighths lower hnlo)
    (fw_actual_index_ratio_of_aggregate lower upper hnlo (by omega) hcount) hVpos hV

/-- The complete existing conservative WW4 envelope from the aggregate
count bound. This does not supply a trace or establish stage existence. -/
theorem fw_first_band_ww4_envelopes_of_aggregate
    (lower : RSIndexLower) (upper : RSIndexUpper) (upperSharp : RSIndexUpperSharp)
    {n j : ℕ} {V : ℝ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hj : j ≤ 238)
    (hcount : OddPrimeCountUniformBound (poolMaximum n : ℝ)
      ((1367 / 250 : ℝ) * (Real.sqrt (poolMaximum n : ℝ) /
        Real.log (poolMaximum n : ℝ))))
    (hVlo : (181 / 8 : ℝ) ≤ V) (hVhi : V ≤ 231 / 10) :
    let X : ℝ := poolMaximum n
    let m₀ : ℝ := 403 / 10000
    let qbar : ℝ := 1 / 69780
    let mf : ℝ := ((9999 / 10000 : ℝ) * (7525444 / 10000000)) / V
    let eps : ℝ := 23 / 48 - 3981035 / 10000000
    m₀ * X ≤ ((n * n : ℕ) : ℝ) - 13 - fwEarlyBudget n ∧
    ((6 * (n + 8) : ℕ) : ℝ) ≤ qbar * X ∧
    0 < mf ∧ mf ≤ m₀ - 2 * qbar * j ∧ 0 < eps ∧
    2 * eps * mf^2 ≥ 2 * 6 * qbar := by
  exact fw_first_band_ww4_envelopes upperSharp hnlo hnhi hj
    (fw_poolMaximum_log_gt_181_eighths lower hnlo)
    (fw_actual_index_ratio_of_aggregate lower upper hnlo (by omega) hcount) hVlo hVhi

/-- Instantiating V with the actual log X discharges its range from the
supplied sharp RS upper and RS lower estimates. -/
theorem fw_first_band_ww4_pointwise_envelopes_of_aggregate
    (lower : RSIndexLower) (upper : RSIndexUpper) (upperSharp : RSIndexUpperSharp)
    {n j : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hj : j ≤ 238)
    (hcount : OddPrimeCountUniformBound (poolMaximum n : ℝ)
      ((1367 / 250 : ℝ) * (Real.sqrt (poolMaximum n : ℝ) /
        Real.log (poolMaximum n : ℝ)))) :
    let X : ℝ := poolMaximum n
    let V : ℝ := Real.log X
    let m₀ : ℝ := 403 / 10000
    let qbar : ℝ := 1 / 69780
    let mf : ℝ := ((9999 / 10000 : ℝ) * (7525444 / 10000000)) / V
    let eps : ℝ := 23 / 48 - 3981035 / 10000000
    m₀ * X ≤ ((n * n : ℕ) : ℝ) - 13 - fwEarlyBudget n ∧
    ((6 * (n + 8) : ℕ) : ℝ) ≤ qbar * X ∧
    0 < mf ∧ mf ≤ m₀ - 2 * qbar * j ∧ 0 < eps ∧
    2 * eps * mf^2 ≥ 2 * 6 * qbar := by
  obtain ⟨hVlo, hVhi⟩ := fw_first_band_pointwise_log_bounds upperSharp lower hnlo hnhi
  exact fw_first_band_ww4_envelopes_of_aggregate lower upper upperSharp hnlo hnhi hj
    hcount hVlo hVhi

end
end Sude
