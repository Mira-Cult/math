import Sude.APInterval

/-! Bound the two BMOR endpoint errors by one midpoint square root. -/
namespace Sude
noncomputable section

/-- Concavity of the square root in the exact two-endpoint form used by FW. -/
theorem sqrt_endpoints_le_two_midpoint (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt b + Real.sqrt c ≤ 2 * Real.sqrt ((b + c) / 2) := by
  have hmid : 0 ≤ (b + c) / 2 := by linarith
  have hsb := Real.sq_sqrt hb
  have hsc := Real.sq_sqrt hc
  have hsm := Real.sq_sqrt hmid
  have hbn := Real.sqrt_nonneg b
  have hcn := Real.sqrt_nonneg c
  have hmn := Real.sqrt_nonneg ((b + c) / 2)
  have hdiff := sq_nonneg (Real.sqrt b - Real.sqrt c)
  nlinarith

/-- For a bounded modulus-two bin, FW's midpoint error bound is a valid
lower bound on the number of actual primes from the prescribed pool. -/
theorem bmor_two_pool_interval_midpoint_supply (h : BMORFiniteTheta)
    (upper : RSIndexUpper) (n : ℕ) (b c M : ℝ)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hb : 1 ≤ b) (hbc : b ≤ c) (hcX : c ≤ (poolMaximum n : ℝ))
    (hM : (b + c) / 2 ≤ M) :
    ((c - b) - 2 * (518 / 125 : ℝ) * Real.sqrt M) /
      Real.log (poolMaximum n : ℝ) ≤ (apInterval b c 2 1).card ∧
    ∀ p ∈ apInterval b c 2 1, p ∈ pool n := by
  have hb0 : 0 ≤ b := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hsqrt := sqrt_endpoints_le_two_midpoint b c hb0 hc0
  have hsqrtM : Real.sqrt ((b + c) / 2) ≤ Real.sqrt M := Real.sqrt_le_sqrt hM
  have hnum : (c - b) - 2 * (518 / 125 : ℝ) * Real.sqrt M ≤
      (c - b) - (518 / 125 : ℝ) * (Real.sqrt b + Real.sqrt c) := by linarith
  have hX : (1 : ℝ) ≤ (poolMaximum n : ℝ) := by
    exact_mod_cast (le_trans (by decide : 1 ≤ 2) (poolMaximum_prime n).two_le)
  have hlog : 0 ≤ Real.log (poolMaximum n : ℝ) := Real.log_nonneg hX
  have hs := bmor_two_pool_interval_supply h upper n b c hn hnmax hb hbc hcX
  exact ⟨(div_le_div_of_nonneg_right hnum hlog).trans hs.1, hs.2⟩

end
end Sude
