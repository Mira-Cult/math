import Sude.BGThetaMeanGates
import Sude.OddCountScaledMean
import Sude.FWActualIndexRatio

/-! FW mean and index bounds from an explicitly supplied aggregate odd-prime
    count estimate. No theta-to-count derivation is asserted. -/
namespace Sude
noncomputable section

/-- The actual normalized mean lies inside FW's required interval whenever
the explicit source hypotheses and the FW logarithmic range hold. -/
theorem fw_actual_pool_normalized_mean_of_aggregate (lower : RSIndexLower)
    {n : ℕ} (hn : 19485 ≤ n)
    (hloglo : (181 / 8 : ℝ) ≤ Real.log (poolMaximum n : ℝ))
    (hloghi : Real.log (poolMaximum n : ℝ) ≤ 29)
    (hcount : OddPrimeCountUniformBound (poolMaximum n : ℝ)
      ((1367 / 250 : ℝ) * (Real.sqrt (poolMaximum n : ℝ) /
        Real.log (poolMaximum n : ℝ)))) :
    (243 / 500 : ℝ) ≤ ((Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ)) /
      (poolMaximum n : ℝ) ∧
    ((Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ)) / (poolMaximum n : ℝ) ≤
      (123 / 250 : ℝ) := by
  let u : ℝ := Real.log (poolMaximum n : ℝ)
  let c : ℝ := (1367 / 250 : ℝ) / 65536
  let W : ℝ := 2^32
  let q : ℝ := u * (((n*n : ℕ) : ℝ) / (poolMaximum n : ℝ))
  let m : ℝ := ((Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ)) / (poolMaximum n : ℝ)
  obtain ⟨i, hi, hai, hbi⟩ := fw_mean_cells_cover hloglo hloghi
  let a : ℝ := (181 + (i : ℝ))/8
  let b : ℝ := (182 + (i : ℝ))/8
  have ha : 0 < a := by dsimp [a]; positivity
  have hau : a ≤ u := hai
  have hub : u ≤ b := hbi
  have hW : 0 < W := by dsimp [W]; positivity
  have hc : 0 < c := by dsimp [c]; norm_num
  have hcert := fw_theta_mean_rational_cells i hi
  dsimp only at hcert
  change 0 < fwMeanA b - c ∧
    (243 / 500 : ℝ) < (fwMeanA (2*b)/2 - 2*c - 4*b/W^2)/(fwMeanB a+c) ∧
    (fwMeanB (2*a)/2 + 2*c + fwMeanB a/W)/(fwMeanA b-c) < (123 / 250 : ℝ) at hcert
  have hden : 0 < fwMeanB a + c := by
    have hB : 0 < fwMeanB a := by dsimp [fwMeanB]; positivity
    linarith
  have hnumlo : 0 ≤ fwMeanA (2*b)/2 - 2*c - 4*b/W^2 := by
    have ht := (lt_div_iff₀ hden).mp hcert.2.1
    have hp := mul_pos (by norm_num : (0 : ℝ) < 243 / 500) hden
    linarith
  have hnumhi : 0 ≤ fwMeanB (2*a)/2 + 2*c + fwMeanB a/W := by
    have ha2 : 0 < 2*a := by positivity
    have hb2 : 0 < fwMeanB (2*a) := by dsimp [fwMeanB]; positivity
    have hb1 : 0 < fwMeanB a := by dsimp [fwMeanB]; positivity
    positivity
  have hlog : 22 ≤ Real.log (poolMaximum n : ℝ) := by linarith
  obtain ⟨hXbound, hsqrt⟩ := odd_count_fw_pool_scales lower hn
  have hs := odd_count_mean_scaled_bounds (by omega : 0 < n) hlog hXbound
    (1367 / 250 : ℝ) 65536 (by norm_num) hsqrt hcount hub
  dsimp only at hs
  change 0 < q ∧ fwMeanA u-c ≤ q ∧ q ≤ fwMeanB u+c ∧
    (fwMeanA (2*u)/2-c-c-4*b/W^2)/q ≤ m ∧
    m ≤ (fwMeanB (2*u)/2+c+c+fwMeanB u/W)/q at hs
  have ht := fw_mean_cell_transport ha hau hub hW hs.1 hs.2.1 hs.2.2.1
    (le_refl c) (le_refl c) (le_refl (4*b/W^2)) (le_refl (fwMeanB u/W))
    hcert.1 hnumlo hnumhi hs.2.2.2.1 hs.2.2.2.2
  change (243 / 500 : ℝ) ≤ m ∧ m ≤ (123 / 250 : ℝ)
  constructor <;> linarith [hcert.2.1, hcert.2.2, ht.1, ht.2]

/-- The same result in the unnormalized form required by FW matched bins. -/
theorem fw_actual_pool_mean_bounds_of_aggregate (lower : RSIndexLower)
    {n : ℕ} (hn : 19485 ≤ n)
    (hloglo : (181 / 8 : ℝ) ≤ Real.log (poolMaximum n : ℝ))
    (hloghi : Real.log (poolMaximum n : ℝ) ≤ 29)
    (hcount : OddPrimeCountUniformBound (poolMaximum n : ℝ)
      ((1367 / 250 : ℝ) * (Real.sqrt (poolMaximum n : ℝ) /
        Real.log (poolMaximum n : ℝ)))) :
    (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤
      (Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ) ∧
    (Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ) ≤
      (123 / 250 : ℝ) * (poolMaximum n : ℝ) := by
  have hX : 0 < (poolMaximum n : ℝ) := by
    exact_mod_cast (poolMaximum_prime n).pos
  have h := fw_actual_pool_normalized_mean_of_aggregate lower hn hloglo hloghi hcount
  exact ⟨(le_div_iff₀ hX).mp h.1, (div_le_iff₀ hX).mp h.2⟩

/-- FW3's index-ratio inequality follows from the explicitly supplied aggregate count estimate
and the RS index hypotheses throughout FW's order
range. The ratio itself is not an assumption. -/
theorem fw_actual_index_ratio_of_aggregate
    (lower : RSIndexLower) (upper : RSIndexUpper) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hcount : OddPrimeCountUniformBound (poolMaximum n : ℝ)
      ((1367 / 250 : ℝ) * (Real.sqrt (poolMaximum n : ℝ) /
        Real.log (poolMaximum n : ℝ)))) :
    Real.log (poolMaximum n : ℝ) - 9/8 <
      (poolMaximum n : ℝ) / (n : ℝ)^2 := by
  let X : ℝ := poolMaximum n
  let N : ℝ := (n*n : ℕ)
  let u : ℝ := Real.log X
  let c : ℝ := (1367 / 250 : ℝ) / 65536
  have hn : 0 < n := by omega
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Nat.mul_pos hn hn
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hlo : (181/8 : ℝ) ≤ u := (fw_poolMaximum_log_gt_181_eighths lower hnlo).le
  have hhi : u ≤ 29 := (fw_poolMaximum_log_lt_29 upper hnlo hnhi).le
  have hu : 0 < u := by linarith
  have hs : 0 ≤ u - 9/8 := by linarith
  have hlog : 22 ≤ Real.log (poolMaximum n : ℝ) := by dsimp [u, X] at *; linarith
  obtain ⟨hXbound, hsqrt⟩ := odd_count_fw_pool_scales lower hnlo
  have hb := odd_count_mean_scaled_bounds hn hlog hXbound
    (1367 / 250 : ℝ) 65536 (by norm_num) hsqrt hcount hhi
  dsimp only at hb
  have hq : u * (N/X) ≤ fwMeanB u + c := hb.2.2.1
  have hmul := mul_le_mul_of_nonneg_left hq hs
  have hgate := fw_theta_index_ratio_rational_gate hlo hhi
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
