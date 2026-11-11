import Sude.FWWheelFirstBandPointwise
import Sude.FWActualIndexRatio

/-! Convert the conservative first-band normalized WW4 quota into the
absolute-count form used by the mixed affine-wheel candidate stage.
The frozen band's majorant and trace existence remain separate. -/
namespace Sude
noncomputable section

/-- The pointwise first-band envelope implies the affine candidate quota
for the actual absolute stock floor `mf * X`. -/
theorem fw_mixed_first_band_affine_quota
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) :
    let X : ℝ := poolMaximum n
    let V : ℝ := Real.log X
    let mf : ℝ := ((9999 / 10000 : ℝ) * (7525444 / 10000000)) / V
    ((6 * (6 * (n + 8)) : ℕ) : ℝ) * X ≤
      (1 / (2 * (1 + 1 / 23)) - 3981035 / 10000000 : ℝ) * (mf * X)^2 := by
  dsimp only
  let X : ℝ := poolMaximum n
  let V : ℝ := Real.log X
  let mf : ℝ := ((9999 / 10000 : ℝ) * (7525444 / 10000000)) / V
  let eps : ℝ := 23 / 48 - 3981035 / 10000000
  let qbar : ℝ := 1 / 69780
  have hlog := fw_poolMaximum_log_gt_181_eighths lower hnlo
  have hratio := fw_actual_index_ratio bmor lower upper hnlo (by omega : n ≤ 35733)
  obtain ⟨hVlo, hVhi⟩ := fw_first_band_pointwise_log_bounds upperSharp lower hnlo hnhi
  have he := fw_first_band_ww4_envelopes upperSharp hnlo hnhi (j := 0) (by omega)
    hlog hratio hVlo hVhi
  dsimp only at he
  change _ ∧ (((6 * (n + 8) : ℕ) : ℝ) ≤ qbar * X) ∧
    0 < mf ∧ mf ≤ _ ∧ 0 < eps ∧ 2 * eps * mf^2 ≥ 2 * 6 * qbar at he
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hQ : (((6 * (n + 8) : ℕ) : ℝ) * X) ≤ qbar * X^2 := by
    have h := mul_le_mul_of_nonneg_right he.2.1 hX.le
    nlinarith
  have hm : 6 * qbar * X^2 ≤ eps * mf^2 * X^2 := by
    have hh : 6 * qbar ≤ eps * mf^2 := by linarith [he.2.2.2.2.2]
    exact mul_le_mul_of_nonneg_right hh (sq_nonneg X)
  have hid : (1 / (2 * (1 + 1 / 23)) - 3981035 / 10000000 : ℝ) = eps := by
    dsimp [eps]; norm_num
  rw [hid]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hQ
  change 6 * (6 * ((n + 8 : ℕ) : ℝ)) * X ≤ eps * (mf * X)^2
  calc
    _ = 6 * ((6 * ((n + 8 : ℕ) : ℝ)) * X) := by ring
    _ ≤ 6 * (qbar * X^2) := mul_le_mul_of_nonneg_left hQ (by norm_num)
    _ ≤ eps * (mf * X)^2 := by nlinarith [hm]

end
end Sude
