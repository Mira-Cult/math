import Sude.FWUniformStockStrong
import Sude.FWStockRoundingGate
import Sude.FWSharpIndex
import Sude.FWEarlyBudgetMargin

/-! FW10 budget margin from the weaker index bound and sharp RS premise. -/
namespace Sude
noncomputable section

/-- The FW10 early budget satisfies the real stock margin, conditional on
an internal index-to-pool inequality. The corollary below derives it from
the explicit sharp RS hypothesis. This theorem does not establish that an
actual removed set meets the budget. -/
theorem fw_early_budget_real_margin_of_twenty_one
    (upper : RSIndexUpper) (lower : RSIndexLower) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hindex : (21 : ℝ) * (n : ℝ) ^ 2 ≤ (poolMaximum n : ℝ)) :
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
  have hbudget : (fwEarlyBudget n : ℝ) ≤ (9 / 2000 : ℝ) * X := by
    have hi : (21 : ℝ) * N ^ 2 ≤ X := hindex
    dsimp [fwEarlyBudget]
    push_cast
    change 12 * (N + 8) * (21 + 3 * ((n / 450 : ℕ) : ℝ)) ≤ (9 / 2000 : ℝ) * X
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
theorem fw_early_budget_floored_square_gate_of_twenty_one
    (upper : RSIndexUpper) (lower : RSIndexLower) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hindex : (21 : ℝ) * (n : ℝ) ^ 2 ≤ (poolMaximum n : ℝ)) :
    (16 : ℝ) * (poolMaximum n : ℝ) <
      (((16 * fwUniformNaturalStock (poolMaximum n) - fwEarlyBudget n : ℕ) : ℝ) ^ 2) := by
  apply fw_uniform_floored_stock_square_gate (poolMaximum n) (fwEarlyBudget n)
    (by exact_mod_cast Nat.zero_le (poolMaximum n))
  exact fw_early_budget_real_margin_of_twenty_one upper lower hnlo hnhi hindex


/-- The sharper published RS index hypothesis supplies the weaker index
condition for FW10; it remains an explicit premise in the type. -/
theorem fw_early_budget_real_margin_of_sharp_index
    (upper : RSIndexUpper) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    (fwEarlyBudget n : ℝ) + 16 + 4 * Real.sqrt (poolMaximum n : ℝ) ≤
      16 * fwUniformRealStock (poolMaximum n : ℝ) := by
  apply fw_early_budget_real_margin_of_twenty_one upper lower hnlo hnhi
  exact le_of_lt (fw_poolMaximum_gt_twenty_one_sq sharp hnlo)

/-- The corresponding rounded gate, retaining all three explicit published
index hypotheses. No actual removed-set accounting is asserted. -/
theorem fw_early_budget_floored_square_gate_of_sharp_index
    (upper : RSIndexUpper) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    (16 : ℝ) * (poolMaximum n : ℝ) <
      (((16 * fwUniformNaturalStock (poolMaximum n) - fwEarlyBudget n : ℕ) : ℝ) ^ 2) := by
  apply fw_early_budget_floored_square_gate_of_twenty_one upper lower hnlo hnhi
  exact le_of_lt (fw_poolMaximum_gt_twenty_one_sq sharp hnlo)

end
end Sude
