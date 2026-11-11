import Sude.FWAffineMixedWheelCertificates
import Sude.FWAffineWheelThreshold
import Sude.FWWheelFirstBandPointwise

/-! First affine-wheel origin gate for the first FW band. This bound does not
prove that the frozen mixed recipe reaches the required radius. -/
namespace Sude
noncomputable section

/-- In the first band, the actual-log stock floor makes the first source
wheel's fixed affine origin less than 1104. -/
theorem fw_first_affine_origin_lt_1104
    (lower : RSIndexLower) (upperSharp : RSIndexUpperSharp) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) :
    let X : ℝ := poolMaximum n
    let V : ℝ := Real.log X
    let mf : ℝ := ((9999 / 10000 : ℝ) * (7525444 / 10000000)) / V
    fwAffineOrigin (fwMixedWheelError 0) 1 X (3981035 / 10000000) (mf * X) < 1104 := by
  dsimp only
  let X : ℝ := poolMaximum n
  let V : ℝ := Real.log X
  let mf : ℝ := ((9999 / 10000 : ℝ) * (7525444 / 10000000)) / V
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  obtain ⟨hVlo, hVhi⟩ := fw_first_band_pointwise_log_bounds upperSharp lower hnlo hnhi
  have hVpos : 0 < V := by dsimp [V, X]; linarith
  have hm : (3257 / 100000 : ℝ) ≤ mf := by
    dsimp [mf]
    apply (le_div_iff₀ hVpos).2
    dsimp [V, X] at *
    nlinarith
  have hmpos : 0 < mf := by linarith
  have heta : (0 : ℝ) < 3981035 / 10000000 := by norm_num
  have hid : fwAffineOrigin (fwMixedWheelError 0) 1 X (3981035 / 10000000) (mf * X) =
      (1 / 2 + fwMixedWheelError 0) / ((3981035 / 10000000 : ℝ) * mf) := by
    unfold fwAffineOrigin
    field_simp
  rw [hid]
  apply (div_lt_iff₀ (mul_pos heta hmpos)).2
  norm_num [fwMixedWheelError] at *
  nlinarith

/-- Any actual radius at least 1104 satisfies the first affine source's
positive-shift gate; obtaining that radius remains an independent obligation. -/
theorem fw_first_affine_shift_of_radius_1104
    (lower : RSIndexLower) (upperSharp : RSIndexUpperSharp) {n R : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hR : 1104 ≤ R) :
    let X : ℝ := poolMaximum n
    let V : ℝ := Real.log X
    let mf : ℝ := ((9999 / 10000 : ℝ) * (7525444 / 10000000)) / V
    0 < (R : ℝ) - fwAffineOrigin (fwMixedWheelError 0) 1 X
      (3981035 / 10000000) (mf * X) := by
  have ho := fw_first_affine_origin_lt_1104 lower upperSharp hnlo hnhi
  have hRr : (1104 : ℝ) ≤ R := by exact_mod_cast hR
  dsimp only at ho ⊢
  linarith

end
end Sude
