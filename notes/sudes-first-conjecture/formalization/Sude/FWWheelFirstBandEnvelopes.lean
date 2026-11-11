import Sude.FWWheelFirstBandFW3

/-! Conservative first-band FW13 stock and quota envelopes. These are
pointwise sufficient inequalities, not identities with the frozen source's
band constants. FW3, the sharp RS upper estimate, the V range and the stage
cap are explicitly supplied; no trace or source analytic theorem is asserted. -/
namespace Sude
noncomputable section

/-- The sharp RS upper-index input bounds X by `22.501*n²` in the first FW
band. -/
theorem fw_first_band_upper_index_ratio (upper : RSIndexUpperSharp) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) :
    (poolMaximum n : ℝ) ≤ (22501 / 1000 : ℝ) * (n : ℝ)^2 := by
  have hnloR : (19485 : ℝ) ≤ n := by exact_mod_cast hnlo
  have hnhiR : (n : ℝ) ≤ 21248 := by exact_mod_cast hnhi
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hjpos : 0 < j := by dsimp [j]; positivity
  have hjone : 1 < j := by dsimp [j]; push_cast; nlinarith
  have hjbound : j ≤ (2 : ℝ)^29 * (7 / 8) := by dsimp [j]; push_cast; norm_num; nlinarith
  have hlogratio : Real.log (7 / 8 : ℝ) ≤ -(1 / 8 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 7 / 8)
    norm_num at h ⊢
    linarith
  have hlogj : Real.log j < 20 := by
    have h := Real.log_le_log hjpos hjbound
    rw [Real.log_mul (by positivity : (2 : ℝ)^29 ≠ 0) (by norm_num : (7 / 8 : ℝ) ≠ 0),
      Real.log_pow] at h
    norm_num at h
    linarith [Real.log_two_lt_d9]
  have hlog20 : Real.log (20 : ℝ) < 3 := by
    have h : (20 : ℝ) = 5 * 2^2 := by norm_num
    rw [h, Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) (by positivity : (2 : ℝ)^2 ≠ 0),
      Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hlogjpos : 0 < Real.log j := Real.log_pos hjone
  have hloglogj : Real.log (Real.log j) < 3 := by
    have h := Real.log_le_log hlogjpos (le_of_lt hlogj)
    linarith
  have hfactor : Real.log j + Real.log (Real.log j) - 1 / 2 < (45 / 2 : ℝ) := by linarith
  have hu := poolMaximum_upper_sharp upper n (by nlinarith)
  change (poolMaximum n : ℝ) < j * (Real.log j + Real.log (Real.log j) - 1 / 2) at hu
  have hprod := mul_lt_mul_of_pos_left hfactor hjpos
  dsimp [j] at hu hprod
  push_cast at hu hprod
  nlinarith

/-- FW10's exact natural-floor budget is at most 0.093 n² on the lower FW
range. -/
theorem fw_first_band_early_budget_bound {n : ℕ} (hn : 19485 ≤ n) :
    (fwEarlyBudget n : ℝ) ≤ (93 / 1000 : ℝ) * (n : ℝ)^2 := by
  let N : ℝ := n
  have hN : (19485 : ℝ) ≤ N := by dsimp [N]; exact_mod_cast hn
  have hdiv : ((n / 450 : ℕ) : ℝ) * 450 ≤ N := by
    dsimp [N]
    exact_mod_cast Nat.div_mul_le_self n 450
  have hfirst : N + 8 ≤ (2001 / 2000 : ℝ) * N := by linarith
  have hsecond : 21 + 3 * ((n / 450 : ℕ) : ℝ) ≤ (1549 / 200000 : ℝ) * N := by linarith
  have hprod := mul_le_mul hfirst hsecond (by positivity : 0 ≤ 21 + 3 * ((n / 450 : ℕ) : ℝ))
    (by positivity : 0 ≤ (2001 / 2000 : ℝ) * N)
  change (fwEarlyBudget n : ℝ) ≤ (93 / 1000 : ℝ) * N^2
  dsimp [fwEarlyBudget]
  push_cast
  change 12 * (N + 8) * (21 + 3 * ((n / 450 : ℕ) : ℝ)) ≤ (93 / 1000 : ℝ) * N^2
  nlinarith

/-- A conservative initial stock baseline, derived from the source RS upper
index estimate and the exact early budget. -/
theorem fw_first_band_stock_baseline (upper : RSIndexUpperSharp) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) :
    (403 / 10000 : ℝ) * (poolMaximum n : ℝ) ≤
      ((n * n : ℕ) : ℝ) - 13 - fwEarlyBudget n := by
  have hnR : (19485 : ℝ) ≤ n := by exact_mod_cast hnlo
  have hindex := fw_first_band_upper_index_ratio upper hnlo hnhi
  have hbudget := fw_first_band_early_budget_bound hnlo
  have hsquare : (100000 : ℝ) * 13 ≤ (n : ℝ)^2 := by nlinarith
  push_cast
  nlinarith

/-- The explicit FW3 ratio gives the 1/69780 upper envelope for the actual
per-stage Q/X charge throughout the first band. -/
theorem fw_first_band_stage_charge_from_fw3 {n : ℕ}
    (hn : 19485 ≤ n)
    (hlog : (181 / 8 : ℝ) < Real.log (poolMaximum n : ℝ))
    (hratio : Real.log (poolMaximum n : ℝ) - 9 / 8 <
      (poolMaximum n : ℝ) / (n : ℝ)^2) :
    ((6 * (n + 8) : ℕ) : ℝ) ≤ (1 / 69780 : ℝ) * poolMaximum n := by
  have hnR : (19485 : ℝ) ≤ n := by exact_mod_cast hn
  have hx := fw_poolMaximum_index_ratio_of_fw3 (show 0 < n by omega) hlog hratio
  push_cast
  nlinarith

/-- Conservative numeric WW4 inputs throughout all 238 declared first-band
steps, using explicit analytic and V-range hypotheses. The envelopes need not
coincide with the frozen checker's band constants. -/
theorem fw_first_band_ww4_envelopes (upper : RSIndexUpperSharp) {n j : ℕ} {V : ℝ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hj : j ≤ 238)
    (hlog : (181 / 8 : ℝ) < Real.log (poolMaximum n : ℝ))
    (hratio : Real.log (poolMaximum n : ℝ) - 9 / 8 <
      (poolMaximum n : ℝ) / (n : ℝ)^2)
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
  dsimp only
  have hVpos : 0 < V := by linarith
  have hmfloat : ((9999 / 10000 : ℝ) * (7525444 / 10000000)) / V ≤
      ((9999 / 10000 : ℝ) * (7525444 / 10000000)) / (181 / 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hVlo
  have hmflower : (3257 / 100000 : ℝ) ≤
      ((9999 / 10000 : ℝ) * (7525444 / 10000000)) / V := by
    apply (le_div_iff₀ hVpos).2
    nlinarith
  have hmf2 := pow_le_pow_left₀ (show (0 : ℝ) ≤ 3257 / 100000 by norm_num) hmflower 2
  have heps : (0 : ℝ) < 23 / 48 - 3981035 / 10000000 := by norm_num
  have hprod := mul_le_mul_of_nonneg_left hmf2 heps.le
  have hrat : (23 / 48 - 3981035 / 10000000 : ℝ) * (3257 / 100000 : ℝ)^2 ≥
      6 / 69780 := by norm_num
  have hjR : (j : ℝ) ≤ 238 := by exact_mod_cast hj
  refine ⟨fw_first_band_stock_baseline upper hnlo hnhi,
    fw_first_band_stage_charge_from_fw3 hnlo hlog hratio, ?_, ?_, heps, ?_⟩
  · positivity
  · norm_num at hmfloat ⊢
    linarith
  · nlinarith

end
end Sude
