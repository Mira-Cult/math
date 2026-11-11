import Sude.Coverage
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! Exact source FW4 quota and allocation-depth gates. -/
namespace Sude

/-- FW's four bands use sixteen retained seed stages and two seed strata.
The largest band endpoint dominates all four source seed-pair quotas. This is
an arithmetic gate only; the finite twin-prime population is not assumed or
proved here. -/
theorem fw_seed_quota_gate (nUpper : ℕ) (hn : nUpper ≤ 35733) :
    6 * (nUpper + 8) * (16 + 2 - 1) ≤ 3650551 := by omega

/-- Every order in the FW range satisfies the source's binary allocation
ceiling. `Nat.clog 2` is the integer ceiling of the base-two logarithm. -/
theorem fw_allocation_depth_gate (n : ℕ) (hn : n ≤ 35733) :
    Nat.clog 2 (6 * n) ≤ 18 := by
  apply Nat.clog_le_of_le_pow
  norm_num
  omega

/-- The FW floor replacement is valid for every integer order in a band,
without differentiating across a floor or checking only endpoints. -/
theorem fw_floor_capacity (n n0 C : ℕ) (hC : 0 < C) (hn0 : 0 < n0) (hn : n0 ≤ n) :
    (n : ℝ) * (1 - (C : ℝ) / n0) / C ≤ ((n / C : ℕ) : ℝ) := by
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC
  have hn0R : (0 : ℝ) < n0 := by exact_mod_cast hn0
  have hnR : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : 1 ≤ (n : ℝ) / n0 := (le_div_iff₀ hn0R).2 (by simpa using hnR)
  have heqNat := Nat.div_add_mod n C
  have heq : (n : ℝ) = C * ((n / C : ℕ) : ℝ) + ((n % C : ℕ) : ℝ) := by exact_mod_cast heqNat.symm
  have hrem : ((n % C : ℕ) : ℝ) < C := by exact_mod_cast Nat.mod_lt n hC
  have hbound : (n : ℝ) / C - 1 ≤ ((n / C : ℕ) : ℝ) := by
    have h := (div_le_iff₀ hCR).2 (show (n : ℝ) ≤ (((n / C : ℕ) : ℝ) + 1) * C by nlinarith)
    linarith
  have hid : (n : ℝ) * (1 - (C : ℝ) / n0) / C = (n : ℝ) / C - (n : ℝ) / n0 := by
    field_simp
  rw [hid]
  linarith

/-- Exact FW reflected-band geometry for the frozen parameters
`A = 235`, `N = 16`, including the endpoint-margin coefficient. -/
theorem fw_reflected_band_geometry :
    let δ : ℝ := 1 / 235
    let w : ℝ := 16 / 235
    let a : ℝ := w + 1 / 3
    0 < δ ∧ δ < 1 / 24 ∧ δ ≤ w ∧
    0 < 243 / 500 - a - w - δ ∧ 123 / 250 + a + w + δ < 1 ∧
    3 * (2 * a - 2 * w) = 2 ∧ 2 * a + 2 * w < 1 := by
  norm_num

end Sude
