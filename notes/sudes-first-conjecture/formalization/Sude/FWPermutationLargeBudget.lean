import Sude.FWPermutationLargeUnion

/-! Numerical FW large-cut budget, for the unrestricted permutation sample. -/
namespace Sude
noncomputable section

/-- A tangent-line upper bound for the logarithm gives the required decay
uniformly from the lower end of FW's order range onward. -/
theorem fw_large_cut_log_gate {x : ℝ} (hx : 19485 ≤ x) :
    6 * Real.log (x + 1) + Real.log 189 < x / 250 := by
  have hxpos : 0 < x + 1 := by linarith
  have hlog2 : Real.log 2 < (7 : ℝ) / 10 := by linarith [Real.log_two_lt_d9]
  have hlog189 : Real.log 189 ≤ 8 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 189)
      (by norm_num : (189 : ℝ) ≤ 2 ^ 8)
    rw [Real.log_pow] at h
    norm_num at h ⊢
    exact h
  have hratio : 0 < (x + 1) / 32768 := by positivity
  have htangent := Real.log_le_sub_one_of_pos hratio
  have hlog : Real.log (x + 1) = 15 * Real.log 2 + Real.log ((x + 1) / 32768) := by
    have hfactor : x + 1 = (2 : ℝ)^15 * ((x + 1) / 32768) := by norm_num; ring
    rw [hfactor, Real.log_mul (by positivity : (2 : ℝ)^15 ≠ 0) (ne_of_gt hratio),
      Real.log_pow]
    norm_num
  rw [hlog]
  linarith

/-- The FW large-cut exponential estimate costs strictly less than `1/189`
for all natural orders at least 19485. -/
theorem fw_large_cut_decay {n : ℕ} (hn : 19485 ≤ n) :
    ((n + 1 : ℕ) : ℝ)^6 * Real.exp (-(n : ℝ) / 250) < 1 / 189 := by
  have hnR : (19485 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hgate := fw_large_cut_log_gate hnR
  have hpowexp : Real.exp (6 * Real.log (((n + 1 : ℕ) : ℝ))) =
      ((n + 1 : ℕ) : ℝ)^6 := by
    rw [show (6 : ℝ) = (6 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hnpos]
  have hexp189 : Real.exp (Real.log 189) = 189 := Real.exp_log (by norm_num)
  have hexp : ((n + 1 : ℕ) : ℝ)^6 * 189 * Real.exp (-(n : ℝ) / 250) < 1 := by
    have h := (Real.exp_lt_exp).2
      (show 6 * Real.log (((n + 1 : ℕ) : ℝ)) + Real.log 189 - (n : ℝ) / 250 < 0 by
        push_cast
        linarith)
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, hpowexp, hexp189, Real.exp_zero] at h
    simpa [neg_div] using h
  nlinarith

/-- Integer cardinality budget for the full event including complementary cuts. -/
theorem fw_large_cut_union_integer_budget {n : ℕ} (hn : 19485 ≤ n) :
    189 * (fwPermutationLargeCutBad n).card < (n.factorial)^3 := by
  have hsum := (fw_large_cut_union_bound (show 0 < n by omega)).trans_lt (fw_large_cut_decay hn)
  have hF : 0 < (n.factorial : ℝ)^3 := pow_pos (by exact_mod_cast Nat.factorial_pos n) _
  have hreal : (189 : ℝ) * ((fwPermutationLargeCutBad n).card : ℝ) <
      (n.factorial : ℝ)^3 := by
    have h := (div_lt_iff₀ hF).1 hsum
    nlinarith
  exact_mod_cast hreal

end
end Sude
