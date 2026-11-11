import Sude.FWUniformStockStrong
import Sude.FWStockRoundingGate

/-! A conditional FW10 budget margin at the source's fixed parameters. -/
namespace Sude
noncomputable section

/-- FW10 early deletion budget for `Q_s=6(n+8)`, `J=5`, `s=16`, and
`K=⌊n/450⌋`. The four frozen FW bands use these same parameters. -/
def fwEarlyBudget (n : ℕ) : ℕ := 12 * (n + 8) * (21 + 3 * (n / 450))

/-- The FW10 early budget satisfies the real stock margin, conditional on
an internal index-to-pool inequality. The latter is an unproved project
obligation here, not an additional published analytic import. This theorem
does not establish that an actual removed set meets the budget. -/
theorem fw_early_budget_real_margin
    (upper : RSIndexUpper) (lower : RSIndexLower) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hindex : (43 / 2 : ℝ) * (n : ℝ) ^ 2 ≤ (poolMaximum n : ℝ)) :
    (fwEarlyBudget n : ℝ) + 16 + 4 * Real.sqrt (poolMaximum n : ℝ) ≤
      16 * fwUniformRealStock (poolMaximum n : ℝ) := by
  let X : ℝ := poolMaximum n
  let N : ℝ := n
  have hN : (19485 : ℝ) ≤ N := by dsimp [N]; exact_mod_cast hnlo
  have hN0 : 0 ≤ N := by linarith
  have hdivnat := Nat.div_mul_le_self n 450
  have hdiv : ((n / 450 : ℕ) : ℝ) * 450 ≤ N := by
    dsimp [N]
    exact_mod_cast hdivnat
  have hfirst : N + 8 ≤ (1001 / 1000 : ℝ) * N := by linarith
  have hsecond : 21 + 3 * ((n / 450 : ℕ) : ℝ) ≤ (7 / 900 : ℝ) * N := by linarith
  have hproduct : (N + 8) * (21 + 3 * ((n / 450 : ℕ) : ℝ)) ≤
      ((1001 / 1000 : ℝ) * N) * ((7 / 900 : ℝ) * N) := by
    exact mul_le_mul hfirst hsecond (by positivity) (by positivity)
  have hbudget : (fwEarlyBudget n : ℝ) ≤ (11 / 2500 : ℝ) * X := by
    have hi : (43 / 2 : ℝ) * N ^ 2 ≤ X := hindex
    dsimp [fwEarlyBudget]
    push_cast
    change 12 * (N + 8) * (21 + 3 * ((n / 450 : ℕ) : ℝ)) ≤ (11 / 2500 : ℝ) * X
    nlinarith
  have hXnat : 2 ^ 32 ≤ poolMaximum n := by
    have h := le_of_lt (fw_poolMaximum_gt_four_seed lower hnlo)
    norm_num at h ⊢
    exact h
  have hX : (4294967296 : ℝ) ≤ X := by dsimp [X]; exact_mod_cast hXnat
  have hX0 : 0 ≤ X := by linarith
  have hprod : 0 ≤ X * (X - 4294967296) := mul_nonneg hX0 (by linarith)
  have hsqrt : Real.sqrt X ≤ X / 65536 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hstock : X / 3500 ≤ fwUniformRealStock X :=
    fw_poolMaximum_uniform_stock_ge_one_over_3500 upper lower hnlo hnhi
  nlinarith

/-- The conditional real margin pays for floor rounding and yields the exact
natural-subtraction square gate needed by FW physical supply. -/
theorem fw_early_budget_floored_square_gate
    (upper : RSIndexUpper) (lower : RSIndexLower) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hindex : (43 / 2 : ℝ) * (n : ℝ) ^ 2 ≤ (poolMaximum n : ℝ)) :
    (16 : ℝ) * (poolMaximum n : ℝ) <
      (((16 * fwUniformNaturalStock (poolMaximum n) - fwEarlyBudget n : ℕ) : ℝ) ^ 2) := by
  apply fw_uniform_floored_stock_square_gate (poolMaximum n) (fwEarlyBudget n)
    (by exact_mod_cast Nat.zero_le (poolMaximum n))
  exact fw_early_budget_real_margin upper lower hnlo hnhi hindex

end
end Sude
