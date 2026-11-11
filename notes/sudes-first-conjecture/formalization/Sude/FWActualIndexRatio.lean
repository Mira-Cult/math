import Sude.FWActualPoolMeanRange

/-! The FW3 index ratio from the same explicit q=4 count and RS hypotheses.
No source index-ratio conclusion is assumed. -/
namespace Sude
noncomputable section

/-- A single exact rational gate covers the whole FW logarithmic interval. -/
theorem fw_index_ratio_rational_gate {u : ℝ}
    (hlo : (181 / 8 : ℝ) ≤ u) (hhi : u ≤ 29) :
    (u - 9/8) * (fwMeanB u + (281649 / 62500 : ℝ) / 65536) < u := by
  let c : ℝ := (281649 / 62500 : ℝ) / 65536
  have hu : 0 < u := by linarith
  have h1 : (23 / 8 : ℝ) / u ≤ (23 / 8 : ℝ) / (181 / 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlo
  have h2 : (9 / 2 : ℝ) / 29^2 ≤ (9 / 2 : ℝ) / u^2 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hu 2)
      (pow_le_pow_left₀ hu.le hhi 2)
  have h3 : c * (u - 9 / 8) ≤ c * (29 - 9 / 8) := by
    apply mul_le_mul_of_nonneg_left (by linarith)
    dsimp [c]; norm_num
  have hnum : (0 : ℝ) < 1/8 - (23/8)/(181/8) + (9/2)/29^2 - c*(29-9/8) := by
    dsimp [c]; norm_num
  have hid : u - (u - 9/8) * (fwMeanB u + c) =
      1/8 - (23/8)/u + (9/2)/u^2 - c*(u-9/8) := by
    dsimp [fwMeanB]
    field_simp
    ring
  rw [← sub_pos, hid]
  linarith

/-- FW3's index-ratio inequality follows from the explicit q=4 finite
prime-count computation and the RS index hypotheses throughout FW's order
range. The ratio itself is not an assumption. -/
theorem fw_actual_index_ratio (bmor : BMORFinitePiFour)
    (lower : RSIndexLower) (upper : RSIndexUpper) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    Real.log (poolMaximum n : ℝ) - 9/8 <
      (poolMaximum n : ℝ) / (n : ℝ)^2 := by
  let X : ℝ := poolMaximum n
  let N : ℝ := (n*n : ℕ)
  let u : ℝ := Real.log X
  let c : ℝ := (281649 / 62500 : ℝ) / 65536
  have hn : 0 < n := by omega
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Nat.mul_pos hn hn
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hlo : (181/8 : ℝ) ≤ u := (fw_poolMaximum_log_gt_181_eighths lower hnlo).le
  have hhi : u ≤ 29 := (fw_poolMaximum_log_lt_29 upper hnlo hnhi).le
  have hu : 0 < u := by linarith
  have hs : 0 ≤ u - 9/8 := by linarith
  have hlog : 22 ≤ Real.log (poolMaximum n : ℝ) := by dsimp [u, X] at *; linarith
  have hnat := poolMaximum_below_two_pow_41 upper n (by omega) (by omega)
  have hcap : (poolMaximum n : ℝ) ≤ (4 * 10 ^ 13 : ℝ) := by
    have h : (poolMaximum n : ℝ) < (2 : ℝ)^41 := by exact_mod_cast hnat
    norm_num at h ⊢
    linarith
  have hb := fw_mean_scaled_bounds bmor lower hnlo hlog hcap hhi
  dsimp only at hb
  have hq : u * (N/X) ≤ fwMeanB u + c := hb.2.2.1
  have hmul := mul_le_mul_of_nonneg_left hq hs
  have hgate := fw_index_ratio_rational_gate hlo hhi
  have hprod : (u - 9/8) * (u*(N/X)) < u := lt_of_le_of_lt hmul hgate
  have hdiv := div_lt_div_of_pos_right hprod hu
  have hratio : (u - 9/8) * (N/X) < 1 := by
    have hid : (u - 9/8) * (u*(N/X)) / u = (u - 9/8) * (N/X) := by
      field_simp
    rw [hid, div_self (ne_of_gt hu)] at hdiv
    exact hdiv
  have hscaled : (u - 9/8) * N < X := by
    have hh : ((u - 9/8) * N)/X < 1 := by simpa only [mul_div_assoc] using hratio
    have hh' := (div_lt_iff₀ hX).mp hh
    linarith
  have hfinal : u - 9/8 < X/N := (lt_div_iff₀ hN).2 hscaled
  simpa [X, N, u, Nat.cast_mul, pow_two] using hfinal

end
end Sude
