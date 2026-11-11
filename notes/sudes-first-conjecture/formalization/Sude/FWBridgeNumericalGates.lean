import Sude.FWBridgeNumericalStock
import Sude.FWLogUpper
import Sude.FWPoolBound

/-! Concrete FW bridge selection gates for an empty initial reservation. -/
namespace Sude
noncomputable section

/-- The exact natural stock parameter used for all five nominal stages. -/
def fwBridgeNumericalM (n : ℕ) : ℕ := poolMaximum n / 30000

/-- The source-width BMOR bound pays both the stage's `2k` entries and the
floor-rounded parameter. The source square gate also holds. These are real
numerical inequalities, not an assertion that the analytic hypotheses or
actual batches, physical placement, or a complete grid have been proved. -/
theorem fw_bridge_numerical_gates (upper : RSIndexUpper) (lower : RSIndexLower)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (j : ℕ) (hj : j < 5) :
    ((fwBridgeNumericalM n + 2 * (3 * (n + 8)) : ℕ) : ℝ) ≤
      fwBridgeStockBound (poolMaximum n) (fwBridgeRadius (poolMaximum n) j) ∧
    fwBridgeWidth (poolMaximum n) (fwBridgeRadius (poolMaximum n) j) + 1 <
      (fwBridgeNumericalM n : ℝ) * fwBridgeNumericalM n := by
  let X : ℝ := poolMaximum n
  let N : ℝ := n
  let M : ℕ := fwBridgeNumericalM n
  have hN : (19485 : ℝ) ≤ N := by dsimp [N]; exact_mod_cast hnlo
  have hN0 : 0 ≤ N := by linarith
  have hNprod : 0 ≤ N * (N - 19485) := mul_nonneg hN0 (by linarith)
  have hXnat : 2 ^ 32 ≤ poolMaximum n := by
    have h := le_of_lt (fw_poolMaximum_gt_four_seed lower hnlo)
    norm_num at h ⊢
    exact h
  have hX : (2 : ℝ) ^ 32 ≤ X := by dsimp [X]; exact_mod_cast hXnat
  have hXlarge : (4294967296 : ℝ) ≤ X := by norm_num at hX ⊢; exact hX
  have hX0 : 0 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hlog : Real.log X ≤ 29 :=
    le_of_lt (fw_poolMaximum_log_lt_29 upper hnlo hnhi)
  have hstock := fw_bridge_nominal_stock_bound_ge_linear X hX hlog j hj
  have hwidth := (fw_bridge_nominal_width_bounds X hXpos j hj).2
  let J : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hlogJ : 15 < Real.log J := finitePrefix_log_index_gt_fifteen (by omega)
  have hJprod : 0 ≤ J * (Real.log J - 15) := mul_nonneg hJ (by linarith)
  have hindex : J * Real.log J < X := poolMaximum_lower lower n
  have hJexpr : J = N ^ 2 + 1 := by dsimp [J, N]; push_cast; ring
  have hXindex : 15 * N ^ 2 < X := by rw [hJexpr] at hindex hJprod; nlinarith
  have hcost : (6 : ℝ) * (N + 8) ≤ X / 30000 := by nlinarith
  have hMupperNat : poolMaximum n / 30000 * 30000 ≤ poolMaximum n :=
    Nat.div_mul_le_self (poolMaximum n) 30000
  have hMupperReal : (M : ℝ) * 30000 ≤ X := by
    dsimp [M, fwBridgeNumericalM, X]
    exact_mod_cast hMupperNat
  have hMupper : (M : ℝ) ≤ X / 30000 := by linarith
  have hMlowerNat : poolMaximum n < 30000 * (poolMaximum n / 30000 + 1) := by omega
  have hMlowerReal : X < 30000 * ((M : ℝ) + 1) := by
    dsimp [M, fwBridgeNumericalM, X]
    exact_mod_cast hMlowerNat
  have hMlower : X / 60000 ≤ (M : ℝ) := by linarith
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hsq : 0 ≤ ((M : ℝ) - X / 60000) * ((M : ℝ) + X / 60000) :=
    mul_nonneg (by linarith) (by positivity)
  have hXprod : 0 ≤ X * (X - 4294967296) := mul_nonneg hX0 (by linarith)
  constructor
  · have hcost' : ((2 * (3 * (n + 8)) : ℕ) : ℝ) ≤ X / 30000 := by
      dsimp [N] at hcost
      push_cast
      linarith
    have hsum : (M : ℝ) + ((2 * (3 * (n + 8)) : ℕ) : ℝ) ≤
        fwBridgeStockBound X (fwBridgeRadius X j) := by linarith
    simpa only [Nat.cast_add] using hsum
  · change fwBridgeWidth X (fwBridgeRadius X j) + 1 < (M : ℝ) * M
    nlinarith

/-- The exact per-side budgets used by the five-batch selector when the
initial reservation is empty. No earlier or nonempty reservation is hidden. -/
theorem fw_bridge_empty_initial_gates (upper : RSIndexUpper) (lower : RSIndexLower)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    (∀ j < 5,
      ((fwBridgeNumericalM n + 2 * (3 * (n + 8)) +
        (fwBridgeLowStock (poolMaximum n) (fwBridgeRadius (poolMaximum n) j) ∩ ∅).card : ℕ) : ℝ) ≤
          fwBridgeStockBound (poolMaximum n) (fwBridgeRadius (poolMaximum n) j)) ∧
    (∀ j < 5,
      ((fwBridgeNumericalM n + 2 * (3 * (n + 8)) +
        (fwBridgeHighStock (poolMaximum n) (fwBridgeRadius (poolMaximum n) j) ∩ ∅).card : ℕ) : ℝ) ≤
          fwBridgeStockBound (poolMaximum n) (fwBridgeRadius (poolMaximum n) j)) ∧
    (∀ j < 5,
      fwBridgeWidth (poolMaximum n) (fwBridgeRadius (poolMaximum n) j) + 1 <
        (fwBridgeNumericalM n : ℝ) * fwBridgeNumericalM n) := by
  constructor
  · intro j hj
    simpa using (fw_bridge_numerical_gates upper lower hnlo hnhi j hj).1
  constructor
  · intro j hj
    simpa using (fw_bridge_numerical_gates upper lower hnlo hnhi j hj).1
  · intro j hj
    exact (fw_bridge_numerical_gates upper lower hnlo hnhi j hj).2

end
end Sude
