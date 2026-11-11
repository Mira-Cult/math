import Sude.UpperTailAnalytic

/-!
# Universal Parameter Schedule and Scalar Gates for the Open Upper Tail (`n ≥ 35,735`)

Defines the branch-free parameter schedule, disjoint prime-pool zones in `(0, X]`,
sharp scale envelopes, improved small-modulus / parity analytic lemmas, and concrete scalar
gate lemmas for every stage of the upper-tail `Sude.HasSquare n` construction across all
`n ≥ 35,735`.
-/

namespace Sude

noncomputable section

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

/-! ## Section 1: Universal Branch-Free Schedule Definitions -/

/-- Pool maximum `X = p_{n^2 + 1}` as a real number. -/
def utX (n : ℕ) : ℝ := (poolMaximum n : ℝ)

/-- Prime-number-theorem scale `Y = X / log X`. -/
def utY (n : ℕ) : ℝ := utX n / Real.log (utX n)

/-- Integer doubled logarithm `⌊2 * log X⌋₊`. -/
def utL2X (n : ℕ) : ℕ := ⌊2 * Real.log (utX n)⌋₊

/-- Universal logarithmic scale parameter `Ln = (⌊2 * log X⌋₊ - 25) / 2` (`≥ 11` for `n ≥ 35,735`). -/
def utLn (n : ℕ) : ℕ := (utL2X n - 25) / 2

/-- Retained pair batch size `Q = 6 * n + 4` (`6 * n` ordinary edge pairs + `4` diagonal pairs). -/
def utQ (n : ℕ) : ℕ := 6 * n + 4

/-- Number of equal-gap seed stages on `Pool 2`. -/
def utSeedStages (n : ℕ) : ℕ := utLn n + 4

/-- Seed gap cap `6 * (Ln + 5)`. -/
def utSeedCap (n : ℕ) : ℕ := 6 * (utLn n + 5)

/-- Half-gap cap `3 * (Ln + 5)` (`g = 2 * h0 ≤ utSeedCap n => h0 ≤ utH0Max n`). -/
def utH0Max (n : ℕ) : ℕ := 3 * (utLn n + 5)

/-- Step budget for the first elementary `AP` narrowing subphase `AP_1` on `Pool 1`
(reaches `15 * utLn n * g`). -/
def utStepsAP1 (n : ℕ) : ℕ := 7 * utLn n

/-- Step budget for the second elementary `AP` narrowing subphase `AP_2` on `Pool 1`
(reaches `12000 * utLn n * g`). -/
def utStepsAP2 (n : ℕ) : ℕ := 19 * utLn n

/-- Total step budget for the elementary `AP` narrowing phase on `Pool 1` (`26 * Ln`). -/
def utStepsAP (n : ℕ) : ℕ := utStepsAP1 n + utStepsAP2 n

/-- Step budget for the Montgomery–Vaughan narrowing phase `MV` on `Pool 2`
(reaches `(76 / 1000) * X` directly). -/
def utStepsMV (n : ℕ) : ℕ := 26 * utLn n + 2 * (utLn n - 11) * utLn n

/-- Extra step-grid radius booster stages on `Pool 2` (`0` for `utLn n ≤ 13`,
`(utH0Max n)^2 / 30 + 1` for `utLn n ≥ 14`), ensuring `R_g - R_mod ≥ (10 / 1000) * X`
with fixed-width `(12 / 10000) * X` `ModCover` bins across all `n ≥ 35,735`. -/
def utStepsBoost (n : ℕ) : ℕ :=
  if utLn n ≤ 13 then 0 else (utH0Max n * utH0Max n) / 30 + 1

/-- Maximum rounds per ordinary `ModCover` bin across the `54` fixed-width bins (`= 1` for `utLn n ≤ 13`). -/
def utModRounds (n : ℕ) : ℕ := (utH0Max n + 53) / 54

/-- Ordinary wide stage count `n / 430 + 12`. -/
def utWOrd (n : ℕ) : ℕ := n / 430 + 12

/-- Diagonal wide stage count `n / 2000 + Ln` (giving `Ω(n * X)` diagonal overlap at all scales). -/
def utWDiag (n : ℕ) : ℕ := n / 2000 + utLn n

/-- Midpoint balancing sub-bin width `(128 / 1000) * X` (`z = 2` sub-bins cover `255 / 1000 * X`). -/
def utMidWidth (n : ℕ) : ℝ := (128 / 1000 : ℝ) * utX n

/-! ## Section 2: Disjoint Prime Zones in `(0, X]` -/

/-- `WideLow` bin `m < 30`: `((4/1000 + 2/1000 * m) * X, (4/1000 + 2/1000 * (m + 1)) * X]`. -/
def utWideLowLo (n m : ℕ) : ℝ := (4 / 1000 + (2 / 1000 : ℝ) * (m : ℝ)) * utX n
def utWideLowHi (n m : ℕ) : ℝ := (4 / 1000 + (2 / 1000 : ℝ) * ((m : ℝ) + 1)) * utX n

/-- `Pool 1`: `(68/1000 * X, 323/1000 * X]` (width `255/1000 * X`). -/
def utPool1Lo (n : ℕ) : ℝ := (68 / 1000 : ℝ) * utX n
def utPool1Hi (n : ℕ) : ℝ := (323 / 1000 : ℝ) * utX n

/-- Contiguous `ModCover` zone `(852/1000 * X, 918/1000 * X]` (total width `(66/1000) * X`),
partitioned into `55` fixed-width `(12 / 10000) * X` bins (`j < 54` for ordinary `ModCover`,
`j = 54` split at `utModBinMid` for diagonal `ModCover`). -/
def utModBinLo (n j : ℕ) : ℝ :=
  (852 / 1000 + (12 / 10000 : ℝ) * (j : ℝ)) * utX n

def utModBinHi (n j : ℕ) : ℝ :=
  (852 / 1000 + (12 / 10000 : ℝ) * ((j : ℝ) + 1)) * utX n

def utModBinMid (n j : ℕ) : ℝ :=
  (852 / 1000 + (12 / 10000 : ℝ) * ((j : ℝ) + 1 / 2)) * utX n

/-- Base fractional low-bin endpoints for the `10` Doubling stages (`k : Fin 10`). -/
def utDblLowFrac (k : Fin 10) : ℝ :=
  match k.val with
  | 0 => 836 / 1000
  | 1 => 837 / 1000
  | 2 => 838 / 1000
  | 3 => 323 / 1000
  | 4 => 325 / 1000
  | 5 => 839 / 1000
  | 6 => 840 / 1000
  | 7 => 326 / 1000
  | 8 => 578 / 1000
  | _ => 351 / 1000

/-- Base fractional high-bin endpoints for the `10` Doubling stages (`k : Fin 10`). -/
def utDblHighFrac (k : Fin 10) : ℝ :=
  match k.val with
  | 0 => 844 / 1000
  | 1 => 849 / 1000
  | 2 => 851 / 1000
  | 3 => 354 / 1000
  | 4 => 353 / 1000
  | 5 => 925 / 1000
  | 6 => 934 / 1000
  | 7 => 579 / 1000
  | 8 => 935 / 1000
  | _ => 936 / 1000

def utDblLowLo (n : ℕ) (k : Fin 10) : ℝ := utDblLowFrac k * utX n
def utDblLowHi (n : ℕ) (k : Fin 10) : ℝ := (utDblLowFrac k + 1 / 1000) * utX n
def utDblHighLo (n : ℕ) (k : Fin 10) : ℝ := utDblHighFrac k * utX n
def utDblHighHi (n : ℕ) (k : Fin 10) : ℝ := (utDblHighFrac k + 1 / 1000) * utX n

/-- Cumulative span lower bound `(B_k - A_0) / X` before Doubling step `k : Fin 10`
(starting at `(76/1000 - 66/1000) = 100/10000`). -/
def utDblSpanFrac (k : Fin 10) : ℝ :=
  match k.val with
  | 0 => 100 / 10000
  | 1 => 170 / 10000
  | 2 => 280 / 10000
  | 3 => 400 / 10000
  | 4 => 700 / 10000
  | 5 => 970 / 10000
  | 6 => 1820 / 10000
  | 7 => 2750 / 10000
  | 8 => 5270 / 10000
  | _ => 8830 / 10000

/-- Central completion keepout zone `(355/1000 * X, 578/1000 * X]`. -/
def utKeepoutLo (n : ℕ) : ℝ := (355 / 1000 : ℝ) * utX n
def utKeepoutHi (n : ℕ) : ℝ := (578 / 1000 : ℝ) * utX n

/-- `Pool 2`: `(581/1000 * X, 836/1000 * X]` (width `255/1000 * X`). -/
def utPool2Lo (n : ℕ) : ℝ := (581 / 1000 : ℝ) * utX n
def utPool2Hi (n : ℕ) : ℝ := (836 / 1000 : ℝ) * utX n

/-- `WideHigh` bin `m < 30`: `((938/1000 + 2/1000 * m) * X, (938/1000 + 2/1000 * (m + 1)) * X]`. -/
def utWideHighLo (n m : ℕ) : ℝ := (938 / 1000 + (2 / 1000 : ℝ) * (m : ℝ)) * utX n
def utWideHighHi (n m : ℕ) : ℝ := (938 / 1000 + (2 / 1000 : ℝ) * ((m : ℝ) + 1)) * utX n

/-- Exact step-gap recurrence verification for all `10` Doubling stages (`k : Fin 10`). -/
theorem ut_dbl_frac_recurrence :
    (∀ k : Fin 10,
      323 / 1000 ≤ utDblLowFrac k ∧
      utDblLowFrac k + 1 / 1000 < utDblHighFrac k ∧
      utDblHighFrac k + 1 / 1000 ≤ 937 / 1000 ∧
      (utDblHighFrac k + 1 / 1000) - utDblLowFrac k ≤ utDblSpanFrac k) ∧
    (∀ k : Fin 9,
      utDblSpanFrac k.succ =
        utDblSpanFrac k.castSucc + (utDblHighFrac k.castSucc - (utDblLowFrac k.castSucc + 1 / 1000))) ∧
    utDblSpanFrac ⟨9, by decide⟩ +
      (utDblHighFrac ⟨9, by decide⟩ - (utDblLowFrac ⟨9, by decide⟩ + 1 / 1000)) = 14670 / 10000 := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    fin_cases k <;> norm_num [utDblLowFrac, utDblHighFrac, utDblSpanFrac]
  · intro k
    fin_cases k <;> norm_num [utDblLowFrac, utDblHighFrac, utDblSpanFrac]
  · norm_num [utDblLowFrac, utDblHighFrac, utDblSpanFrac]

/-- All `20` Doubling bins are pairwise disjoint and avoid `WideLow`, `Pool 1`, `ModZone`,
`Keepout`, `Pool 2`, and `WideHigh`. -/
theorem ut_dbl_bins_disjoint_and_separated :
    let dInterval : Fin 10 × Bool → ℝ × ℝ := fun kb =>
      if kb.2 then (utDblHighFrac kb.1, utDblHighFrac kb.1 + 1 / 1000)
      else (utDblLowFrac kb.1, utDblLowFrac kb.1 + 1 / 1000)
    (∀ x y : Fin 10 × Bool, x ≠ y → (dInterval x).2 ≤ (dInterval y).1 ∨ (dInterval y).2 ≤ (dInterval x).1) ∧
    (∀ x : Fin 10 × Bool,
      323 / 1000 ≤ (dInterval x).1 ∧
      (dInterval x).2 ≤ 938 / 1000 ∧
      ((dInterval x).2 ≤ 355 / 1000 ∨ 578 / 1000 ≤ (dInterval x).1) ∧
      ((dInterval x).2 ≤ 581 / 1000 ∨ 836 / 1000 ≤ (dInterval x).1) ∧
      ((dInterval x).2 ≤ 852 / 1000 ∨ 918 / 1000 ≤ (dInterval x).1)) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · rintro ⟨k1, b1⟩ ⟨k2, b2⟩ hne
    fin_cases k1 <;> fin_cases b1 <;> fin_cases k2 <;> fin_cases b2
    all_goals first
      | exact False.elim (hne rfl)
      | (dsimp [utDblLowFrac, utDblHighFrac]; norm_num)
  · rintro ⟨k, b⟩
    fin_cases k <;> fin_cases b <;> (dsimp [utDblLowFrac, utDblHighFrac]; norm_num)

/-! ## Section 3: Sharp Parity & Small-Modulus Analytic Helpers -/

/-- Across all scales `x ≥ 10 ^ 8`, `|thetaAP x 2 1 - x| ≤ x / 2400`. -/
theorem thetaAP_mod_two_all_ge_1e8
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    {x : ℝ} (hx : (10 ^ 8 : ℝ) ≤ x) :
    |thetaAP x 2 1 - x| ≤ x / 2400 := by
  by_cases hcap : x ≤ (4 * 10 ^ 13 : ℝ)
  · have hx1 : (1 : ℝ) ≤ x := by linarith
    have hbmor := bmor_theta_two_via_four bmor x hx1 hcap
    have hs_ge : (10000 : ℝ) ≤ Real.sqrt x := by
      have hsq : (10000 : ℝ) ^ 2 ≤ x := by
        linarith [show (10000 : ℝ) ^ 2 ≤ 10 ^ 8 by norm_num]
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 10000)]
      exact Real.sqrt_le_sqrt hsq
    have hsqrt_le : Real.sqrt x ≤ x / 10000 := by
      have hmul : (10000 : ℝ) * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hs_ge (Real.sqrt_nonneg x)
      rw [Real.mul_self_sqrt (by linarith)] at hmul
      linarith
    linarith
  · have h7e12 : (7 * 10 ^ 12 : ℝ) ≤ x := by linarith
    have himp := bmor_theta_mod_two_all_ge_7e12 imp h7e12
    linarith

/-- Odd-prime interval lower bound for `10 ^ 8 ≤ b ≤ c ≤ X`. -/
theorem apInterval_mod_two_card_lower_ge_1e8
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    {b c X : ℝ} (hb : (10 ^ 8 : ℝ) ≤ b) (hbc : b ≤ c) (hcX : c ≤ X) :
    ((c - b) - (b + c) / 2400) / Real.log X ≤ (apInterval b c 2 1).card := by
  have hX1 : 1 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos hX1
  have hupper := thetaAP_interval_le_count_log b c X 2 1 (by linarith) hbc hcX
  have hB := (abs_le.mp (thetaAP_mod_two_all_ge_1e8 bmor imp hb)).2
  have hC := (abs_le.mp (thetaAP_mod_two_all_ge_1e8 bmor imp (hb.trans hbc))).1
  rw [div_le_iff₀ hlog]
  linarith

/-- Across all scales `x ≥ 10 ^ 9`, `|thetaAP x 2 1 - x| ≤ x / 7600`. -/
theorem thetaAP_mod_two_all_ge_1e9
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    {x : ℝ} (hx : (10 ^ 9 : ℝ) ≤ x) :
    |thetaAP x 2 1 - x| ≤ x / 7600 := by
  by_cases hcap : x ≤ (4 * 10 ^ 13 : ℝ)
  · have hx1 : (1 : ℝ) ≤ x := by linarith
    have hbmor := bmor_theta_two_via_four bmor x hx1 hcap
    have hs_ge : (31622 : ℝ) ≤ Real.sqrt x := by
      have hsq : (31622 : ℝ) ^ 2 ≤ x := by
        linarith [show (31622 : ℝ) ^ 2 ≤ 10 ^ 9 by norm_num]
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 31622)]
      exact Real.sqrt_le_sqrt hsq
    have hsqrt_le : Real.sqrt x ≤ x / 31622 := by
      have hmul : (31622 : ℝ) * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hs_ge (Real.sqrt_nonneg x)
      rw [Real.mul_self_sqrt (by linarith)] at hmul
      linarith
    linarith
  · have h7e12 : (7 * 10 ^ 12 : ℝ) ≤ x := by linarith
    have himp := bmor_theta_mod_two_all_ge_7e12 imp h7e12
    linarith

/-- Odd-prime interval lower bound for `10 ^ 9 ≤ b ≤ c ≤ X`. -/
theorem apInterval_mod_two_card_lower_ge_1e9
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    {b c X : ℝ} (hb : (10 ^ 9 : ℝ) ≤ b) (hbc : b ≤ c) (hcX : c ≤ X) :
    ((c - b) - (b + c) / 7600) / Real.log X ≤ (apInterval b c 2 1).card := by
  have hX1 : 1 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos hX1
  have hupper := thetaAP_interval_le_count_log b c X 2 1 (by linarith) hbc hcX
  have hB := (abs_le.mp (thetaAP_mod_two_all_ge_1e9 bmor imp hb)).2
  have hC := (abs_le.mp (thetaAP_mod_two_all_ge_1e9 bmor imp (hb.trans hbc))).1
  rw [div_le_iff₀ hlog]
  linarith

/-- Across all scales `x ≥ 9 * 10 ^ 9`, `|thetaAP x 2 1 - x| ≤ x / 22000`. -/
theorem thetaAP_mod_two_all_ge_9e9
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    {x : ℝ} (hx : (9 * 10 ^ 9 : ℝ) ≤ x) :
    |thetaAP x 2 1 - x| ≤ x / 22000 := by
  by_cases hcap : x ≤ (4 * 10 ^ 13 : ℝ)
  · have hx1 : (1 : ℝ) ≤ x := by linarith
    have hbmor := bmor_theta_two_via_four bmor x hx1 hcap
    have hs_ge : (94868 : ℝ) ≤ Real.sqrt x := by
      have hsq : (94868 : ℝ) ^ 2 ≤ x := by
        linarith [show (94868 : ℝ) ^ 2 ≤ 9 * 10 ^ 9 by norm_num]
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 94868)]
      exact Real.sqrt_le_sqrt hsq
    have hsqrt_le : Real.sqrt x ≤ x / 94868 := by
      have hmul : (94868 : ℝ) * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hs_ge (Real.sqrt_nonneg x)
      rw [Real.mul_self_sqrt (by linarith)] at hmul
      linarith
    linarith
  · have h7e12 : (7 * 10 ^ 12 : ℝ) ≤ x := by linarith
    have himp := bmor_theta_mod_two_all_ge_7e12 imp h7e12
    linarith

/-- Sharp odd-prime interval lower bound for `9 * 10 ^ 9 ≤ b ≤ c ≤ X`. -/
theorem apInterval_mod_two_card_lower_ge_9e9
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    {b c X : ℝ} (hb : (9 * 10 ^ 9 : ℝ) ≤ b) (hbc : b ≤ c) (hcX : c ≤ X) :
    ((c - b) - (b + c) / 22000) / Real.log X ≤ (apInterval b c 2 1).card := by
  have hX1 : 1 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos hX1
  have hupper := thetaAP_interval_le_count_log b c X 2 1 (by linarith) hbc hcX
  have hB := (abs_le.mp (thetaAP_mod_two_all_ge_9e9 bmor imp hb)).2
  have hC := (abs_le.mp (thetaAP_mod_two_all_ge_9e9 bmor imp (hb.trans hbc))).1
  rw [div_le_iff₀ hlog]
  linarith

/-- Across all scales `x ≥ 2 * 10 ^ 10`, `|thetaAP x 2 1 - x| ≤ x / 24000`. -/
theorem thetaAP_mod_two_all_ge_2e10
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    {x : ℝ} (hx : (2 * 10 ^ 10 : ℝ) ≤ x) :
    |thetaAP x 2 1 - x| ≤ x / 24000 := by
  by_cases hcap : x ≤ (4 * 10 ^ 13 : ℝ)
  · have hx1 : (1 : ℝ) ≤ x := by linarith
    have hbmor := bmor_theta_two_via_four bmor x hx1 hcap
    have hs_ge : (141421 : ℝ) ≤ Real.sqrt x := by
      have hsq : (141421 : ℝ) ^ 2 ≤ x := by
        linarith [show (141421 : ℝ) ^ 2 ≤ 2 * 10 ^ 10 by norm_num]
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 141421)]
      exact Real.sqrt_le_sqrt hsq
    have hsqrt_le : Real.sqrt x ≤ x / 141421 := by
      have hmul : (141421 : ℝ) * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hs_ge (Real.sqrt_nonneg x)
      rw [Real.mul_self_sqrt (by linarith)] at hmul
      linarith
    linarith
  · have h7e12 : (7 * 10 ^ 12 : ℝ) ≤ x := by linarith
    exact bmor_theta_mod_two_all_ge_7e12 imp h7e12

/-- Sharp odd-prime interval lower bound for `2 * 10 ^ 10 ≤ b ≤ c ≤ X`. -/
theorem apInterval_mod_two_card_lower_ge_2e10
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    {b c X : ℝ} (hb : (2 * 10 ^ 10 : ℝ) ≤ b) (hbc : b ≤ c) (hcX : c ≤ X) :
    ((c - b) - (b + c) / 24000) / Real.log X ≤ (apInterval b c 2 1).card := by
  have hX1 : 1 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos hX1
  have hupper := thetaAP_interval_le_count_log b c X 2 1 (by linarith) hbc hcX
  have hB := (abs_le.mp (thetaAP_mod_two_all_ge_2e10 bmor imp hb)).2
  have hC := (abs_le.mp (thetaAP_mod_two_all_ge_2e10 bmor imp (hb.trans hbc))).1
  rw [div_le_iff₀ hlog]
  linarith

/-- Across all scales `x ≥ 5 * 10 ^ 9`, for any `q ∈ [3, 36]` with `2 ≤ φ(q)` and `gcd(q, a) = 1`,
`|thetaAP x q a - x / φ(q)| ≤ x / 25000`. -/
theorem thetaAP_small_moduli_ge_two_all_scales
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    {q : ℕ} {a : ℤ} {x : ℝ}
    (hq_min : 3 ≤ q) (hq_max : q ≤ 36) (hphi : 2 ≤ Nat.totient q)
    (hcop : Nat.Coprime q a.natAbs) (hx : (5 * 10 ^ 9 : ℝ) ≤ x) :
    |thetaAP x q a - x / (Nat.totient q : ℝ)| ≤ x / 25000 := by
  have hphiR : (2 : ℝ) ≤ (Nat.totient q : ℝ) := by exact_mod_cast hphi
  have hphi_ub : (Nat.totient q : ℝ) ≤ 36 := by
    have hle : Nat.totient q ≤ 36 := (Nat.totient_le q).trans hq_max
    exact_mod_cast hle
  by_cases hcap : x ≤ (10 ^ 13 : ℝ)
  · have hx1 : (1 : ℝ) ≤ x := by linarith
    have hbmor := bmor_theta_bounded bmor q a x hq_min (by omega) hcop hx1 hcap
    have hs_ge : (70710 : ℝ) ≤ Real.sqrt x := by
      have hsq : (70710 : ℝ) ^ 2 ≤ x := by
        linarith [show (70710 : ℝ) ^ 2 ≤ 5 * 10 ^ 9 by norm_num]
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 70710)]
      exact Real.sqrt_le_sqrt hsq
    have hsqrt_le : Real.sqrt x ≤ x / 70710 := by
      have hmul : (70710 : ℝ) * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hs_ge (Real.sqrt_nonneg x)
      rw [Real.mul_self_sqrt (by linarith)] at hmul
      linarith
    linarith
  · have h7e12 : (7 * 10 ^ 12 : ℝ) ≤ x := by linarith
    have hx_pos : 0 < x := by linarith
    have hpi_lo : (314 / 100 : ℝ) < Real.pi := by
      have h := Real.pi_gt_d2; norm_num at h ⊢; exact h
    have hpi_hi : Real.pi < (315 / 100 : ℝ) := by
      have h := Real.pi_lt_d2; norm_num at h ⊢; exact h
    have hlog2_lo : (6931471803 / 10000000000 : ℝ) < Real.log 2 := by
      have h := Real.log_two_gt_d9; norm_num at h ⊢; exact h
    have hlog2_hi : Real.log 2 < (6931471808 / 10000000000 : ℝ) := by
      have h := Real.log_two_lt_d9; norm_num at h ⊢; exact h
    have hlam_lo : (18 : ℝ) ≤ Real.log (10 ^ 8 : ℝ) := by
      have hle : (2 : ℝ) ^ 26 ≤ 10 ^ 8 := by norm_num
      have h := Real.log_le_log (by positivity) hle
      rw [Real.log_pow] at h; push_cast at h; linarith
    have hlam_hi : Real.log (10 ^ 8 : ℝ) ≤ 19 := by
      have hle : (10 ^ 8 : ℝ) ≤ (2 : ℝ) ^ 27 := by norm_num
      have h := Real.log_le_log (by positivity) hle
      rw [Real.log_pow (2 : ℝ) 27] at h; push_cast at h; linarith
    have hlog_lo : (28 : ℝ) ≤ Real.log x := by
      have h2_42 : (2 : ℝ) ^ 42 ≤ x := by linarith [show (2 : ℝ) ^ 42 ≤ 7 * 10 ^ 12 by norm_num]
      have h := Real.log_le_log (by positivity) h2_42
      rw [Real.log_pow] at h; push_cast at h; linarith
    have hs_ge : (2645751 : ℝ) ≤ Real.sqrt x := by
      have hsq : (2645751 : ℝ) ^ 2 ≤ x := by linarith [show (2645751 : ℝ) ^ 2 ≤ 7 * 10 ^ 12 by norm_num]
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2645751)]
      exact Real.sqrt_le_sqrt hsq
    have hsqrt_le : Real.sqrt x ≤ x / 2645751 := by
      have hmul : (2645751 : ℝ) * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hs_ge (Real.sqrt_nonneg x)
      rw [Real.mul_self_sqrt hx_pos.le] at hmul; linarith
    have hlog_sub : 25 * Real.log x + 62 ≤ (1 / 10 : ℝ) * Real.sqrt x := by
      let s := Real.sqrt x
      have hs_pos : 0 < s := by dsimp [s]; linarith
      let r0 := Real.sqrt s
      have hr0_ge : (1626 : ℝ) ≤ r0 := by
        have hsq : (1626 : ℝ) ^ 2 ≤ s := by
          dsimp [s]; linarith [show (1626 : ℝ) ^ 2 ≤ 2645751 by norm_num]
        dsimp [r0]
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1626)]
        exact Real.sqrt_le_sqrt hsq
      have hr0_pos : 0 < r0 := by linarith
      have hr0_le : r0 ≤ s / 1626 := by
        have hmul : (1626 : ℝ) * r0 ≤ r0 * r0 := mul_le_mul_of_nonneg_right hr0_ge hr0_pos.le
        rw [Real.mul_self_sqrt hs_pos.le] at hmul; linarith
      have hlog_r0 : Real.log r0 ≤ r0 - 1 := Real.log_le_sub_one_of_pos hr0_pos
      have hlog_s : Real.log s = 2 * Real.log r0 := by
        dsimp [r0]; rw [Real.log_sqrt hs_pos.le]; ring
      have hlog_x : Real.log x = 2 * Real.log s := by
        dsimp [s]; rw [Real.log_sqrt hx_pos.le]; ring
      linarith
    have hK0 : bmorLowZeroCap (36 : ℝ) ((10 ^ 8 : ℝ) / 36) ≤ 68 := by
      unfold bmorLowZeroCap bmorC1 bmorC2
      dsimp only
      let ν := Real.log (36 : ℝ)
      let lam := Real.log ((36 : ℝ) * ((10 ^ 8 : ℝ) / 36))
      let c := Real.log (2 * Real.pi) + 1
      have hν_hi : ν ≤ 5 := by
        have hle : (36 : ℝ) ≤ (2 : ℝ) ^ 6 := by norm_num
        have h := Real.log_le_log (by positivity) hle
        rw [Real.log_pow] at h; dsimp [ν]; push_cast at h; linarith
      have hc_lo : (2 : ℝ) ≤ c := by
        have h4 : (2 : ℝ) ^ 2 ≤ 2 * Real.pi := by linarith
        have h := Real.log_le_log (by positivity) h4
        rw [Real.log_pow] at h; dsimp [c]; push_cast at h; linarith
      have hlam_eq : lam = Real.log (10 ^ 8 : ℝ) := by dsimp [lam]; congr 1; norm_num
      have hlam_hi' : lam ≤ 19 := by rw [hlam_eq]; exact hlam_hi
      have hlam_lo' : c ≤ lam := by
        rw [hlam_eq]
        have h2pi : 2 * Real.pi ≤ (2 : ℝ) ^ 3 := by linarith
        have h := Real.log_le_log (by positivity) h2pi
        rw [Real.log_pow] at h; dsimp [c]; push_cast at h; linarith
      have hquad1 : (ν - c) - (ν - c) ^ 2 / 2 ≤ 1 / 2 := by
        have hsq : 0 ≤ ((ν - c) - 1) ^ 2 := sq_nonneg _
        linarith
      have hdiff_hi : lam - c ≤ 17 := by linarith
      have hdiff_lo : 0 ≤ lam - c := by linarith
      have hquad2 : (lam - c) + (lam - c) ^ 2 / 2 ≤ 17 + 17 ^ 2 / 2 := by nlinarith
      have hnum : (ν - c) + (lam - c) + ((lam - c) ^ 2 - (ν - c) ^ 2) / 2 ≤ 162 := by linarith
      have hdiv : ((ν - c) + (lam - c) + ((lam - c) ^ 2 - (ν - c) ^ 2) / 2) / Real.pi ≤
          162 / (314 / 100 : ℝ) := by
        have h1 : ((ν - c) + (lam - c) + ((lam - c) ^ 2 - (ν - c) ^ 2) / 2) / Real.pi ≤
            162 / Real.pi := div_le_div_of_nonneg_right hnum (by positivity)
        have h2 : (162 : ℝ) / Real.pi ≤ 162 / (314 / 100 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi_lo.le
        exact h1.trans h2
      change ((ν - c) + (lam - c) + ((lam - c) ^ 2 - (ν - c) ^ 2) / 2) / Real.pi +
        2 * (399 / 1000) * ν + 399 / 1000 + 2 * (5338 / 1000) - (399 / 1000) / ((10 ^ 8 : ℝ) / 36) ≤ 68
      linarith
    have har_lo : (9 : ℝ) ≤ (10 : ℝ) - 28 / (bmorZeroFreeR * (Real.log (10 ^ 8 : ℝ)) ^ 2) := by
      unfold bmorZeroFreeR
      have hsq : (18 : ℝ) ^ 2 ≤ (Real.log (10 ^ 8 : ℝ)) ^ 2 := pow_le_pow_left₀ (by norm_num) hlam_lo 2
      have hmul_sq : (28 / 5 : ℝ) * 18 ^ 2 ≤ (28 / 5 : ℝ) * (Real.log (10 ^ 8 : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
      have hdiv : 28 / ((28 / 5 : ℝ) * (Real.log (10 ^ 8 : ℝ)) ^ 2) ≤ 28 / ((28 / 5 : ℝ) * 18 ^ 2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hmul_sq
      linarith
    have hpt := bmor_theta_small_moduli_pointwise imp
      (q := q) (Q := 36) (a := a) (r := 10) (Φ := (Nat.totient q : ℝ))
      (τ := 4 / 10 ^ 6) (z := 28) (K0 := 68) (x := x)
      hq_min hq_max (by decide) hcop (le_refl _) (by decide) (by linarith) (by norm_num)
      (by norm_num) (by linarith) hK0 (by norm_num) (by linarith) hlog_lo
    have hsmooth : bmorSmoothFactor 10 (4 / 10 ^ 6 : ℝ) ≤ ((4 / 10 ^ 6 : ℝ) ^ 10)⁻¹ * 2048 := by
      unfold bmorSmoothFactor
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hterm : ∀ j ∈ Finset.range 11,
          (Nat.choose 10 j : ℝ) * (1 + (j : ℝ) * (4 / 10 ^ 6 : ℝ)) ^ 11 ≤ (Nat.choose 10 j : ℝ) * 2 := by
        intro j hj
        have hj_le : (j : ℝ) ≤ 10 := by exact_mod_cast (show j ≤ 10 by have := Finset.mem_range.mp hj; omega)
        have h1 : 1 + (j : ℝ) * (4 / 10 ^ 6 : ℝ) ≤ 1 + 10 * (4 / 10 ^ 6 : ℝ) := by nlinarith
        have hp1 : (1 + (j : ℝ) * (4 / 10 ^ 6 : ℝ)) ^ 11 ≤ (1 + 10 * (4 / 10 ^ 6 : ℝ)) ^ 11 :=
          pow_le_pow_left₀ (by positivity) h1 11
        have hp2 : (1 + 10 * (4 / 10 ^ 6 : ℝ)) ^ 11 ≤ 2 := by norm_num
        exact mul_le_mul_of_nonneg_left (hp1.trans hp2) (Nat.cast_nonneg _)
      have hsum_nat : (∑ j ∈ Finset.range 11, Nat.choose 10 j * 2) = 2048 := by decide
      have hsum_real : (∑ j ∈ Finset.range 11, (Nat.choose 10 j : ℝ) * 2) = 2048 := by exact_mod_cast hsum_nat
      exact (Finset.sum_le_sum hterm).trans (le_of_eq hsum_real)
    have hhigh : bmorHighZeroSum (36 : ℝ) (Nat.totient q : ℝ) 28 10 ≤
        (36 / (2 * ((10 ^ 8 : ℝ) / 36) ^ 10)) * 2 := by
      unfold bmorHighZeroSum bmorC1 bmorC2 bmorZeroFreeR
      dsimp only
      have hfac_le : (Nat.totient q : ℝ) / (2 * ((10 ^ 8 : ℝ) / 36) ^ 10) ≤
          36 / (2 * ((10 ^ 8 : ℝ) / 36) ^ 10) :=
        div_le_div_of_nonneg_right hphi_ub (by positivity)
      let lam := Real.log (10 ^ 8 : ℝ)
      let ar := (10 : ℝ) - 28 / ((28 / 5 : ℝ) * lam ^ 2)
      have har9 : 9 ≤ ar := har_lo
      have har_sq : 81 ≤ ar ^ 2 := by nlinarith
      have hBr : (lam / ar + 1 / ar ^ 2) / Real.pi + 2 * (399 / 1000 * lam + 5338 / 1000) / ((10 ^ 8 : ℝ) / 36) ≤ 1 := by
        have h1 : lam / ar ≤ 19 / 9 :=
          (div_le_div_of_nonneg_right hlam_hi (by linarith)).trans
            (div_le_div_of_nonneg_left (by norm_num) (by norm_num) har9)
        have h2 : 1 / ar ^ 2 ≤ 1 / 81 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) har_sq
        have h3 : (lam / ar + 1 / ar ^ 2) / Real.pi ≤ (19 / 9 + 1 / 81) / (314 / 100 : ℝ) :=
          (div_le_div_of_nonneg_right (by linarith) (by positivity)).trans
            (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi_lo.le)
        linarith
      have hBr0 : (lam / 10 + 1 / (10 : ℝ) ^ 2) / Real.pi + 2 * (399 / 1000 * lam + 5338 / 1000) / ((10 ^ 8 : ℝ) / 36) ≤ 1 := by
        have h1 : (lam / 10 + 1 / (10 : ℝ) ^ 2) / Real.pi ≤ (19 / 10 + 1 / 100) / (314 / 100 : ℝ) :=
          (div_le_div_of_nonneg_right (by linarith) (by positivity)).trans
            (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi_lo.le)
        linarith
      have hexp1 : Real.exp (-28 / ((28 / 5 : ℝ) * lam)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith)
      have hexp2 : Real.exp (-28 / 2 : ℝ) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
      have hBr_nn : 0 ≤ (lam / ar + 1 / ar ^ 2) / Real.pi + 2 * (399 / 1000 * lam + 5338 / 1000) / ((10 ^ 8 : ℝ) / 36) := by
        have : 0 < ar := by linarith
        positivity
      have hBr0_nn : 0 ≤ (lam / 10 + 1 / (10 : ℝ) ^ 2) / Real.pi + 2 * (399 / 1000 * lam + 5338 / 1000) / ((10 ^ 8 : ℝ) / 36) := by
        positivity
      have hp1 := mul_le_mul hexp1 hBr hBr_nn (by norm_num)
      have hp2 := mul_le_mul hexp2 hBr0 hBr0_nn (by norm_num)
      have hsum_le : Real.exp (-28 / ((28 / 5 : ℝ) * lam)) *
          ((lam / ar + 1 / ar ^ 2) / Real.pi + 2 * (399 / 1000 * lam + 5338 / 1000) / ((10 ^ 8 : ℝ) / 36)) +
        Real.exp (-28 / 2 : ℝ) *
          ((lam / 10 + 1 / (10 : ℝ) ^ 2) / Real.pi + 2 * (399 / 1000 * lam + 5338 / 1000) / ((10 ^ 8 : ℝ) / 36)) ≤ 2 := by
        linarith
      exact mul_le_mul hfac_le hsum_le (by positivity) (by positivity)
    have hhigh_nn : 0 ≤ bmorHighZeroSum (36 : ℝ) (Nat.totient q : ℝ) 28 10 := by
      unfold bmorHighZeroSum bmorC1 bmorC2 bmorZeroFreeR; dsimp only
      have : 0 < (10 : ℝ) - 28 / ((28 / 5 : ℝ) * (Real.log (10 ^ 8 : ℝ)) ^ 2) := by
        unfold bmorZeroFreeR at har_lo; linarith
      positivity
    have hprod_high : bmorSmoothFactor 10 (4 / 10 ^ 6 : ℝ) *
        bmorHighZeroSum (36 : ℝ) (Nat.totient q : ℝ) 28 10 ≤ 3 / 10 ^ 6 := by
      have h1 := mul_le_mul hsmooth hhigh hhigh_nn (by positivity)
      have h2 : (((4 / 10 ^ 6 : ℝ) ^ 10)⁻¹ * 2048) * ((36 / (2 * ((10 ^ 8 : ℝ) / 36) ^ 10)) * 2) ≤ 3 / 10 ^ 6 := by
        norm_num
      exact h1.trans h2
    have hmul_goal : (Nat.totient q : ℝ) * |thetaAP x q a - x / (Nat.totient q : ℝ)| ≤
        (Nat.totient q : ℝ) * (x / 25000) := by
      have h1 : ((10 : ℕ) * (4 / 10 ^ 6 : ℝ) / 2 +
          bmorSmoothFactor 10 (4 / 10 ^ 6 : ℝ) * bmorHighZeroSum (36 : ℝ) (Nat.totient q : ℝ) 28 10) * x ≤
          (23 / 10 ^ 6 : ℝ) * x := by
        push_cast; nlinarith
      have h2 : (23 / 10 ^ 6 : ℝ) * x ≤ (Nat.totient q : ℝ) * ((23 / 2000000 : ℝ) * x) := by
        nlinarith
      have h3 : (68 * (1 + (10 : ℕ) * (4 / 10 ^ 6 : ℝ) / 2) + 2) * Real.sqrt x +
          (25 * Real.log x + 62) ≤ 71 * Real.sqrt x := by
        push_cast; linarith
      have h4 : (Nat.totient q : ℝ) * (68 * (1 + (10 : ℕ) * (4 / 10 ^ 6 : ℝ) / 2) + 2) * Real.sqrt x +
          (Nat.totient q : ℝ) * (25 * Real.log x + 62) ≤
          (Nat.totient q : ℝ) * (71 * Real.sqrt x) := by
        nlinarith
      have h5 : (23 / 2000000 : ℝ) * x + 71 * Real.sqrt x ≤ x / 25000 := by
        linarith
      have h6 : (Nat.totient q : ℝ) * ((23 / 2000000 : ℝ) * x + 71 * Real.sqrt x) ≤
          (Nat.totient q : ℝ) * (x / 25000) :=
        mul_le_mul_of_nonneg_left h5 (by linarith)
      linarith
    exact le_of_mul_le_mul_left hmul_goal (by linarith)

/-- Convert `b ^ 2 ≤ y ^ 5` into `Real.exp ((2 / 5) * Real.log b) ≤ y`. -/
theorem exp_two_fifths_log_le_of_pow {b y : ℝ} (hb : 0 < b) (hy : 0 ≤ y)
    (hpow : b ^ 2 ≤ y ^ 5) :
    Real.exp ((2 / 5 : ℝ) * Real.log b) ≤ y := by
  have hexp5 : (Real.exp ((2 / 5 : ℝ) * Real.log b)) ^ 5 = b ^ 2 := by
    rw [← Real.exp_nat_mul]
    have hmul : ((5 : ℕ) : ℝ) * ((2 / 5 : ℝ) * Real.log b) = ((2 : ℕ) : ℝ) * Real.log b := by
      push_cast; ring
    rw [hmul, Real.exp_nat_mul, Real.exp_log hb]
  have hle5 : (Real.exp ((2 / 5 : ℝ) * Real.log b)) ^ 5 ≤ y ^ 5 := by
    rw [hexp5]; exact hpow
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le hy (by decide : 5 ≠ 0)).mp hle5

/-- Sharp single-class modulo-`2p` upper bound `((c - b) / 2 + (b + c) / 25000) / Real.log b`
for all primes `p < b` (`p ≤ 17` via BMOR `q ≤ 36`, `p ≥ 19` via Montgomery–Vaughan with
`ell = (2 / 5) * Real.log b`, which needs only `b ^ 2 ≤ ((c - b) / (2 * p)) ^ 5`). -/
theorem apInterval_filter_mod_two_prime_sharp
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports) (mv : MVBrunTitchmarsh)
    {b c : ℝ} {p r : ℕ}
    (hp : Nat.Prime p)
    (hb : (5 * 10 ^ 9 : ℝ) ≤ b)
    (hbc : b < c)
    (hp_lt : (p : ℝ) < b)
    (hexp : Real.exp ((2 / 5 : ℝ) * Real.log b) ≤ (c - b) / (2 * p)) :
    (((apInterval b c 2 1).filter (fun x => x % (2 * p) = r)).card : ℝ) ≤
      ((c - b) / 2 + (b + c) / 25000) / Real.log b := by
  let F := (apInterval b c 2 1).filter (fun x => x % (2 * p) = r)
  have hb0 : 0 ≤ b := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hlog : 0 < Real.log b := Real.log_pos (by linarith)
  by_cases hne : F.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    have hx₀_f := Finset.mem_filter.mp hx₀
    have hx₀_mem := (mem_apInterval_iff b c 2 1 hb0 hc0 x₀).mp hx₀_f.1
    have hx₀_prime : Nat.Prime x₀ := hx₀_mem.1
    have hx₀_gt_b : b < (x₀ : ℝ) := hx₀_mem.2.1
    have hx₀_mod2 : x₀ % 2 = 1 := by exact_mod_cast hx₀_mem.2.2.2
    have hx₀_gt_p : p < x₀ := by exact_mod_cast (hp_lt.trans hx₀_gt_b)
    have hcop_2_x₀ : Nat.Coprime 2 x₀ := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two, Nat.dvd_iff_mod_eq_zero]
      omega
    have hcop_p_x₀ : Nat.Coprime p x₀ := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro hdvd
      rcases (Nat.dvd_prime hx₀_prime).mp hdvd with h1 | heq
      · have := hp.two_le; omega
      · omega
    have hcop_2p_x₀ : Nat.Coprime (2 * p) x₀ :=
      Nat.Coprime.mul_left hcop_2_x₀ hcop_p_x₀
    have hr_eq : r = x₀ % (2 * p) := hx₀_f.2.symm
    have hcop_2p_r : Nat.Coprime (2 * p) r := by
      rw [hr_eq, Nat.Coprime, Nat.gcd_comm, ← Nat.gcd_rec]
      exact hcop_2p_x₀
    have hr_pos : 0 < r := by
      by_contra hr0
      have hr0' : r = 0 := by omega
      rw [hr0', Nat.coprime_zero_right] at hcop_2p_r
      have := hp.two_le; omega
    have hr_lt : r < 2 * p := by rw [hr_eq]; exact Nat.mod_lt x₀ (by have := hp.two_le; omega)
    have hF_sub : F ⊆ apInterval b c (2 * p) (r : ℤ) := by
      intro x hx
      have hxf := Finset.mem_filter.mp hx
      have hxm := (mem_apInterval_iff b c 2 1 hb0 hc0 x).mp hxf.1
      rw [mem_apInterval_iff b c (2 * p) (r : ℤ) hb0 hc0]
      refine ⟨hxm.1, hxm.2.1, hxm.2.2.1, ?_⟩
      have hmod_nat : x % (2 * p) = r % (2 * p) := by
        rw [hxf.2, Nat.mod_eq_of_lt hr_lt]
      exact_mod_cast hmod_nat
    have hF_le : (F.card : ℝ) ≤ (apInterval b c (2 * p) (r : ℤ)).card := by
      exact_mod_cast Finset.card_le_card hF_sub
    by_cases hp17 : p ≤ 17
    · have hq_min : 3 ≤ 2 * p := by have := hp.two_le; omega
      have hq_max : 2 * p ≤ 36 := by omega
      have hphi_ge2 : 2 ≤ Nat.totient (2 * p) := by
        rcases hp.eq_two_or_odd with rfl | hp_odd
        · decide
        · have hcop2 : Nat.Coprime 2 p := by
            rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two, Nat.dvd_iff_mod_eq_zero]; omega
          rw [Nat.totient_mul hcop2, Nat.totient_two, Nat.totient_prime hp, one_mul]
          have := hp.two_le; omega
      have hcopZ : Nat.Coprime (2 * p) (r : ℤ).natAbs := by simpa using hcop_2p_r
      have hB := (abs_le.mp (thetaAP_small_moduli_ge_two_all_scales bmor imp
        hq_min hq_max hphi_ge2 hcopZ hb)).1
      have hC := (abs_le.mp (thetaAP_small_moduli_ge_two_all_scales bmor imp
        hq_min hq_max hphi_ge2 hcopZ (hb.trans hbc.le))).2
      have hcnt := ut_count_log_le_thetaAP_interval b c (2 * p) (r : ℤ) (by linarith) hbc.le
      have hphiR : (2 : ℝ) ≤ (Nat.totient (2 * p) : ℝ) := by exact_mod_cast hphi_ge2
      have hmain_le : (c - b) / (Nat.totient (2 * p) : ℝ) ≤ (c - b) / 2 :=
        div_le_div_of_nonneg_left (by linarith) (by norm_num) hphiR
      have hdiv_cb : c / (Nat.totient (2 * p) : ℝ) - b / (Nat.totient (2 * p) : ℝ) =
          (c - b) / (Nat.totient (2 * p) : ℝ) := by ring
      have hbmor_card : ((apInterval b c (2 * p) (r : ℤ)).card : ℝ) ≤
          ((c - b) / 2 + (b + c) / 25000) / Real.log b := by
        rw [le_div_iff₀ hlog]
        linarith
      exact hF_le.trans hbmor_card
    · have hp19 : 19 ≤ p := by
        by_cases h18 : p = 18
        · subst h18; exact absurd hp (by decide)
        · omega
      have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
      have hcop_2_p : Nat.Coprime 2 p := by
        rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two, Nat.dvd_iff_mod_eq_zero]; omega
      have hphi_2p : Nat.totient (2 * p) = p - 1 := by
        rw [Nat.totient_mul hcop_2_p, Nat.totient_two, Nat.totient_prime hp, one_mul]
      have hphi_ge : (18 : ℝ) ≤ (Nat.totient (2 * p) : ℝ) := by
        rw [hphi_2p]; exact_mod_cast (show 18 ≤ p - 1 by omega)
      have hell_pos : 0 < (2 / 5 : ℝ) * Real.log b := by positivity
      have hk_lt_y : ((2 * p : ℕ) : ℝ) < c - b := by
        have h1 : (1 : ℝ) < Real.exp ((2 / 5 : ℝ) * Real.log b) := Real.one_lt_exp_iff.mpr hell_pos
        have h2 : (1 : ℝ) < (c - b) / (2 * p) := lt_of_lt_of_le h1 hexp
        have hp_pos : (0 : ℝ) < (2 * p : ℝ) := by positivity
        rw [lt_div_iff₀ hp_pos] at h2; push_cast; linarith
      have hsub_eq : apInterval b (b + (c - b)) (2 * p) (r : ℤ) = apInterval b c (2 * p) (r : ℤ) := by
        congr 1; ring
      have hmv := mv_short_interval_subset_bound mv b (c - b) ((2 / 5 : ℝ) * Real.log b)
        (2 * p) r F (by linarith) (by linarith) (by positivity) hr_pos hcop_2p_r hk_lt_y
        hell_pos (by push_cast at hexp ⊢; exact hexp) (by rw [hsub_eq]; exact hF_sub)
      have hden_le : 18 * ((2 / 5 : ℝ) * Real.log b) ≤
          (Nat.totient (2 * p) : ℝ) * ((2 / 5 : ℝ) * Real.log b) :=
        mul_le_mul_of_nonneg_right hphi_ge hell_pos.le
      have hdiv_le : 2 * (c - b) / ((Nat.totient (2 * p) : ℝ) * ((2 / 5 : ℝ) * Real.log b)) ≤
          2 * (c - b) / (18 * ((2 / 5 : ℝ) * Real.log b)) :=
        div_le_div_of_nonneg_left (by linarith) (by positivity) hden_le
      have h5_18 : 2 * (c - b) / (18 * ((2 / 5 : ℝ) * Real.log b)) ≤
          ((c - b) / 2 + (b + c) / 25000) / Real.log b := by
        have hcalc : 2 * (c - b) / (18 * ((2 / 5 : ℝ) * Real.log b)) =
            ((5 / 18 : ℝ) * (c - b)) / Real.log b := by ring
        rw [hcalc]
        exact div_le_div_of_nonneg_right (by linarith) hlog.le
      exact (le_of_lt hmv).trans (hdiv_le.trans h5_18)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    change (F.card : ℝ) ≤ _
    rw [hne, Finset.card_empty, Nat.cast_zero]
    positivity

/-! ## Section 4: Sharp Scale & Elementary Envelopes (`n ≥ 35,735`) -/

/-- Exact prime-count identity at `poolMaximum n`: `primeCountReal (poolMaximum n) = n^2 + 1`. -/
theorem primeCountReal_poolMaximum (n : ℕ) :
    primeCountReal (poolMaximum n : ℝ) = ((n * n : ℕ) : ℝ) + 1 := by
  rw [primeCountReal_natCast_eq_count]
  have hp := poolMaximum_prime n
  have hcnt : Nat.count Nat.Prime (poolMaximum n + 1) = Nat.count Nat.Prime (poolMaximum n) + 1 :=
    Nat.count_succ Nat.Prime (poolMaximum n) |>.trans (by simp [hp])
  have hnth : Nat.count Nat.Prime (poolMaximum n) = n * n :=
    Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime (n * n)
  rw [hcnt, hnth]
  push_cast; ring

/-- Master sharp scale bounds for all `n ≥ 35,735` (internal helper including linear `log X`). -/
private theorem ut_sharp_scale_bounds_aux
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n : ℕ} (hn : 35735 ≤ n) :
    ((24 : ℝ) < Real.log (utX n) ∧
    48 ≤ utL2X n ∧
    11 ≤ utLn n ∧
    (utLn n : ℝ) + 25 / 2 ≤ Real.log (utX n) ∧
    Real.log (utX n) < (utLn n : ℝ) + 27 / 2 ∧
    (925 / 1000 : ℝ) * (n : ℝ) ^ 2 < utY n ∧
    6 * n < 2 ^ (utLn n + 8) ∧
    Nat.clog 2 (6 * n) ≤ utLn n + 8 ∧
    (utLn n : ℝ) ≤ (12 / 35735 : ℝ) * (n : ℝ) ∧
    (utLn n : ℝ) ^ 2 ≤ (144 / 35735 : ℝ) * (n : ℝ)) ∧
    Real.log (utX n) < (68 / 100000 : ℝ) * (n : ℝ) := by
  obtain ⟨hX_sq, hX_283, _, _, _⟩ := poolMaximum_bounds_ge_35735 sharp upper hn
  have hX_pos : 0 < utX n := by dsimp [utX]; linarith
  have hexp1_lt : Real.exp 1 < 27183 / 10000 :=
    lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hexp1_gt : (27182 / 10000 : ℝ) < Real.exp 1 :=
    lt_trans (by norm_num) Real.exp_one_gt_d9
  have hexp24 : Real.exp 24 < utX n := by
    have h1 : Real.exp 24 = (Real.exp 1) ^ 24 := by
      have : (24 : ℝ) = ((24 : ℕ) : ℝ) * 1 := by norm_num
      rw [this, Real.exp_nat_mul]
    rw [h1]
    have h2 : (Real.exp 1) ^ 24 < (27183 / 10000 : ℝ) ^ 24 :=
      pow_lt_pow_left₀ hexp1_lt (Real.exp_pos 1).le (by decide)
    have h3 : (27183 / 10000 : ℝ) ^ 24 < 283 * 10 ^ 8 := by norm_num
    dsimp [utX]; linarith
  have hlogX_gt24 : (24 : ℝ) < Real.log (utX n) := by
    have h := Real.log_lt_log (Real.exp_pos 24) hexp24
    rwa [Real.log_exp] at h
  have h2log_gt48 : (48 : ℝ) < 2 * Real.log (utX n) := by linarith
  have hL2X_ge48 : 48 ≤ utL2X n := Nat.le_floor h2log_gt48.le
  have hLn_ge11 : 11 ≤ utLn n := by dsimp [utLn]; omega
  have hfl_le : (utL2X n : ℝ) ≤ 2 * Real.log (utX n) :=
    Nat.floor_le (by positivity)
  have hfl_lt : 2 * Real.log (utX n) < (utL2X n : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hLn_nat_lo : 2 * utLn n + 25 ≤ utL2X n := by dsimp [utLn]; omega
  have hLn_nat_hi : utL2X n ≤ 2 * utLn n + 26 := by dsimp [utLn]; omega
  have hLn_lo_R : 2 * (utLn n : ℝ) + 25 ≤ (utL2X n : ℝ) := by exact_mod_cast hLn_nat_lo
  have hLn_hi_R : (utL2X n : ℝ) ≤ 2 * (utLn n : ℝ) + 26 := by exact_mod_cast hLn_nat_hi
  have hlogX_lo : (utLn n : ℝ) + 25 / 2 ≤ Real.log (utX n) := by linarith
  have hlogX_hi : Real.log (utX n) < (utLn n : ℝ) + 27 / 2 := by linarith
  have hY_gt : (925 / 1000 : ℝ) * (n : ℝ) ^ 2 < utY n := by
    have hexp32 : Real.exp (3 / 2) < utX n := by
      have hlt : Real.exp (3 / 2) < Real.exp 24 := Real.exp_lt_exp.mpr (by norm_num)
      exact hlt.trans hexp24
    have hrs := rs.upper_sharp (utX n) hexp32
    rw [utX, primeCountReal_poolMaximum n] at hrs
    have hden_pos : 0 < Real.log (poolMaximum n : ℝ) - 3 / 2 := by
      dsimp [utX] at hlogX_gt24; linarith
    rw [lt_div_iff₀ hden_pos] at hrs
    have hlog_pos : 0 < Real.log (utX n) := by linarith
    dsimp [utY, utX] at hlog_pos hlogX_gt24 ⊢
    rw [lt_div_iff₀ hlog_pos]
    have hsq_cast : ((n * n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by push_cast; ring
    rw [hsq_cast] at hrs
    nlinarith
  have hlog2_lo : (6931471803 / 10000000000 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9; norm_num at h ⊢; exact h
  have hlog2_hi : Real.log 2 < (6931471808 / 10000000000 : ℝ) := by
    have h := Real.log_two_lt_d9; norm_num at h ⊢; exact h
  have h6n_pow : 6 * n < 2 ^ (utLn n + 8) := by
    have hn2_pow : (2 : ℝ) ^ 30 < (n : ℝ) ^ 2 := by
      have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith [show (2 : ℝ) ^ 30 < 35735 ^ 2 by norm_num]
    have h2logn_gt : (2079 / 100 : ℝ) < 2 * Real.log (n : ℝ) := by
      have h := Real.log_lt_log (by positivity) hn2_pow
      rw [Real.log_pow, Real.log_pow] at h; push_cast at h; linarith
    have hexp3_lt : Real.exp 3 < 2 * Real.log (n : ℝ) := by
      have h1 : Real.exp 3 = (Real.exp 1) ^ 3 := by
        have : (3 : ℝ) = ((3 : ℕ) : ℝ) * 1 := by norm_num
        rw [this, Real.exp_nat_mul]
      have h2 : (Real.exp 1) ^ 3 < (27183 / 10000 : ℝ) ^ 3 :=
        pow_lt_pow_left₀ hexp1_lt (Real.exp_pos 1).le (by decide)
      rw [h1]; linarith [show (27183 / 10000 : ℝ) ^ 3 < 2079 / 100 by norm_num]
    have hll_gt3 : (3 : ℝ) < Real.log (2 * Real.log (n : ℝ)) := by
      have h := Real.log_lt_log (Real.exp_pos 3) hexp3_lt
      rwa [Real.log_exp] at h
    have hlogX_low_n := poolMaximum_log_lower lower n (by omega)
    change 2 * Real.log (n : ℝ) + Real.log (2 * Real.log (n : ℝ)) < Real.log (utX n) at hlogX_low_n
    have hlogn_ub : Real.log (n : ℝ) < (1 / 2 : ℝ) * (utLn n : ℝ) + 21 / 4 := by linarith
    have hlog6_lt : Real.log 6 < 181 / 100 := by
      have h6_pow : (6 : ℝ) ^ 5 < (2 : ℝ) ^ 13 := by norm_num
      have h := Real.log_lt_log (by positivity) h6_pow
      rw [Real.log_pow, Real.log_pow] at h; push_cast at h; linarith
    have hLnR_ge11 : (11 : ℝ) ≤ (utLn n : ℝ) := by exact_mod_cast hLn_ge11
    have hlog_6n_lt : Real.log (6 * (n : ℝ)) < ((utLn n + 8 : ℕ) : ℝ) * Real.log 2 := by
      rw [Real.log_mul (by norm_num) (by positivity)]
      push_cast; nlinarith
    have hexp_cmp := Real.exp_lt_exp.mpr hlog_6n_lt
    rw [Real.exp_log (by positivity), Real.exp_nat_mul, Real.exp_log (by norm_num)] at hexp_cmp
    exact_mod_cast hexp_cmp
  have hclog : Nat.clog 2 (6 * n) ≤ utLn n + 8 :=
    Nat.clog_le_iff_le_pow (by decide : 1 < 2) |>.mpr h6n_pow.le
  let u : ℝ := (n : ℝ) / 35735
  have hu_ge1 : 1 ≤ u := by
    have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    dsimp [u]; linarith
  have hu_pos : 0 < u := by linarith
  have hlog_u_nn : 0 ≤ Real.log u := Real.log_nonneg hu_ge1
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hj_pos : 0 < j := by dsimp [j]; positivity
  have hj_gt1 : 1 < j := by dsimp [j]; exact_mod_cast (show 1 < n * n + 1 by nlinarith)
  have hj_le_u2 : j ≤ 1276990226 * u ^ 2 := by
    have hn_eq : (n : ℝ) = 35735 * u := by dsimp [u]; ring
    have hj_eq : j = (n : ℝ) ^ 2 + 1 := by dsimp [j]; push_cast; ring
    rw [hj_eq, hn_eq]
    have hu2_ge1 : 1 ≤ u ^ 2 := by nlinarith
    nlinarith
  have hlog_1276 : Real.log 1276990226 < 21 := by
    have hpow : (1276990226 : ℝ) < (Real.exp 1) ^ 21 := by
      have h1 : (1276990226 : ℝ) < (27182 / 10000 : ℝ) ^ 21 := by norm_num
      exact h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide))
    have h := Real.log_lt_log (by norm_num) hpow
    rw [← Real.exp_nat_mul, Real.log_exp] at h
    push_cast at h; linarith
  have hlogj_lt : Real.log j < 21 + 2 * Real.log u := by
    have h1 := Real.log_le_log hj_pos hj_le_u2
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
    push_cast at h1; linarith
  have hlog21_lt : Real.log 21 < 35 / 10 := by
    have h21 : (21 : ℝ) ^ 2 < (Real.exp 1) ^ 7 := by
      have h1 : (21 : ℝ) ^ 2 < (27182 / 10000 : ℝ) ^ 7 := by norm_num
      exact h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide))
    have h := Real.log_lt_log (by norm_num) h21
    rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h
    push_cast at h; linarith
  have hllj_lt : Real.log (Real.log j) < 35 / 10 + Real.log u := by
    have h1 := Real.log_lt_log (Real.log_pos hj_gt1) hlogj_lt
    have h21_eq : 21 + 2 * Real.log u = 21 * (1 + (2 / 21 : ℝ) * Real.log u) := by ring
    have h1p_pos : 0 < 1 + (2 / 21 : ℝ) * Real.log u := by linarith
    rw [h21_eq, Real.log_mul (by norm_num) h1p_pos.ne'] at h1
    have hsub := Real.log_le_sub_one_of_pos h1p_pos
    linarith
  have hsum_j_le : Real.log j + Real.log (Real.log j) < (49 / 2 : ℝ) * (1 + Real.log u / 8) := by
    linarith
  have hu_pow8 : (1 + Real.log u / 8) ^ 8 ≤ u := pow_one_add_log_div_le hu_ge1 8 (by decide)
  have hlog_1p : Real.log (1 + Real.log u / 8) ≤ (1 / 8 : ℝ) * Real.log u := by
    have h1p8_pos : 0 < 1 + Real.log u / 8 := by linarith
    have h := Real.log_le_log (pow_pos h1p8_pos 8) hu_pow8
    rw [Real.log_pow] at h; push_cast at h; linarith
  have hu_pool := poolMaximum_upper upper n (tail_prime_index_domains (by omega : 2001 ≤ n)).1
  have hX_lt_prod : utX n < (1276990226 * (49 / 2) : ℝ) * u ^ 2 * (1 + Real.log u / 8) := by
    dsimp [utX]
    have hp1 := mul_lt_mul_of_pos_left hsum_j_le hj_pos
    have hp2 := mul_le_mul_of_nonneg_right hj_le_u2 (show 0 ≤ (49 / 2 : ℝ) * (1 + Real.log u / 8) by linarith)
    linarith
  have hconst_lt : Real.log (1276990226 * (49 / 2) : ℝ) < 97 / 4 := by
    have hpow : (1276990226 * (49 / 2) : ℝ) ^ 4 < (Real.exp 1) ^ 97 := by
      have h1 : (1276990226 * (49 / 2) : ℝ) ^ 4 < (27182 / 10000 : ℝ) ^ 97 := by norm_num
      exact h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide))
    have h := Real.log_lt_log (by norm_num) hpow
    rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h
    push_cast at h; linarith
  have hlogX_u : Real.log (utX n) < 97 / 4 + (17 / 8 : ℝ) * Real.log u := by
    have h1p8_pos : 0 < 1 + Real.log u / 8 := by linarith
    have h := Real.log_lt_log hX_pos hX_lt_prod
    rw [Real.log_mul (by positivity) h1p8_pos.ne',
        Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
    push_cast at h; linarith
  have hLn_lt_u : (utLn n : ℝ) < 47 / 4 + (17 / 8 : ℝ) * Real.log u := by linarith
  have hLn_le_12half : (utLn n : ℝ) ≤ 12 * (1 + Real.log u / 2) := by linarith
  have hu_pow1 : 1 + Real.log u ≤ u := by
    simpa using pow_one_add_log_div_le hu_ge1 1 (by decide)
  have hu_pow2 : (1 + Real.log u / 2) ^ 2 ≤ u := pow_one_add_log_div_le hu_ge1 2 (by decide)
  have hLn_lin : (utLn n : ℝ) ≤ (12 / 35735 : ℝ) * (n : ℝ) := by
    have h1 : 12 * (1 + Real.log u / 2) ≤ 12 * (1 + Real.log u) := by linarith
    have h2 : 12 * (1 + Real.log u) ≤ 12 * u :=
      mul_le_mul_of_nonneg_left hu_pow1 (by norm_num : (0 : ℝ) ≤ 12)
    have h3 : 12 * u = (12 / 35735 : ℝ) * (n : ℝ) := by dsimp [u]; ring
    linarith
  have hLn_sq : (utLn n : ℝ) ^ 2 ≤ (144 / 35735 : ℝ) * (n : ℝ) := by
    have h1 : (utLn n : ℝ) ^ 2 ≤ (12 * (1 + Real.log u / 2)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hLn_le_12half 2
    have h2 : (12 * (1 + Real.log u / 2)) ^ 2 = 144 * (1 + Real.log u / 2) ^ 2 := by ring
    have h3 : 144 * (1 + Real.log u / 2) ^ 2 ≤ 144 * u :=
      mul_le_mul_of_nonneg_left hu_pow2 (by norm_num : (0 : ℝ) ≤ 144)
    have h4 : 144 * u = (144 / 35735 : ℝ) * (n : ℝ) := by dsimp [u]; ring
    linarith
  have hlogX_lin : Real.log (utX n) < (68 / 100000 : ℝ) * (n : ℝ) := by
    have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : 97 / 4 + (17 / 8 : ℝ) * Real.log u ≤ (97 / 4 : ℝ) * (1 + Real.log u) := by linarith
    have h2 : (97 / 4 : ℝ) * (1 + Real.log u) ≤ (97 / 4 : ℝ) * u :=
      mul_le_mul_of_nonneg_left hu_pow1 (by norm_num)
    have h3 : (97 / 4 : ℝ) * u < (68 / 100000 : ℝ) * (n : ℝ) := by dsimp [u]; linarith
    linarith
  exact ⟨⟨hlogX_gt24, hL2X_ge48, hLn_ge11, hlogX_lo, hlogX_hi, hY_gt,
    h6n_pow, hclog, hLn_lin, hLn_sq⟩, hlogX_lin⟩

/-- Master sharp scale bounds for all `n ≥ 35,735`. -/
theorem ut_sharp_scale_bounds
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n : ℕ} (hn : 35735 ≤ n) :
    (24 : ℝ) < Real.log (utX n) ∧
    48 ≤ utL2X n ∧
    11 ≤ utLn n ∧
    (utLn n : ℝ) + 25 / 2 ≤ Real.log (utX n) ∧
    Real.log (utX n) < (utLn n : ℝ) + 27 / 2 ∧
    (925 / 1000 : ℝ) * (n : ℝ) ^ 2 < utY n ∧
    6 * n < 2 ^ (utLn n + 8) ∧
    Nat.clog 2 (6 * n) ≤ utLn n + 8 ∧
    (utLn n : ℝ) ≤ (12 / 35735 : ℝ) * (n : ℝ) ∧
    (utLn n : ℝ) ^ 2 ≤ (144 / 35735 : ℝ) * (n : ℝ) :=
  (ut_sharp_scale_bounds_aux rs lower sharp upper hn).1

/-- Sharp linear bound `log (utX n) < (68 / 100000) * n` across all `n ≥ 35,735`. -/
theorem ut_logX_lt_linear
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n : ℕ} (hn : 35735 ≤ n) :
    Real.log (utX n) < (68 / 100000 : ℝ) * (n : ℝ) :=
  (ut_sharp_scale_bounds_aux rs lower sharp upper hn).2

/-- Sharp linear envelopes for `utStepsMV n` and `30 * utLn n + utStepsMV n` across all `n ≥ 35,735`. -/
theorem ut_quadratic_step_bounds
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n : ℕ} (hn : 35735 ≤ n) :
    (utStepsMV n : ℝ) ≤ (82 / 10000 : ℝ) * (n : ℝ) ∧
    30 * (utLn n : ℝ) + (utStepsMV n : ℝ) ≤ (1725 / 100000 : ℝ) * (n : ℝ) := by
  obtain ⟨_, _, hLn11, hlogX_lo, _, _, _, _, _, _⟩ :=
    ut_sharp_scale_bounds rs lower sharp upper hn
  have hexp1_gt : (27182 / 10000 : ℝ) < Real.exp 1 :=
    lt_trans (by norm_num) Real.exp_one_gt_d9
  have hXpos : 0 < utX n := by dsimp [utX]; exact_mod_cast (poolMaximum_prime n).pos
  rcases (by omega : utLn n = 11 ∨ 12 ≤ utLn n) with h11 | h12
  · have hs : utStepsMV n = 286 := by simp [utStepsMV, h11]
    have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    rw [hs, h11]; push_cast
    exact ⟨by linarith, by linarith⟩
  · by_cases hn66 : n < 66000
    · have hj6 : 6 ≤ n * n + 1 := (tail_prime_index_domains (by omega : 2001 ≤ n)).1
      let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
      have hj_pos : 0 < j := by dsimp [j]; positivity
      have hj_gt1 : 1 < j := by dsimp [j]; exact_mod_cast (show 1 < n * n + 1 by nlinarith)
      have hn41 : 41000 ≤ n := by
        by_contra hn_lt
        have hn_le : (n : ℝ) ≤ 41000 := by exact_mod_cast (show n ≤ 41000 by omega)
        have hj_lt41 : j ≤ (41000 : ℝ) ^ 2 + 1 := by
          dsimp [j]; push_cast; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
        have hlj41 : Real.log j < 43 / 2 := by
          have hp : j ^ 2 < (Real.exp 1) ^ 43 := by
            have h1 : ((41000 : ℝ) ^ 2 + 1) ^ 2 < (27182 / 10000 : ℝ) ^ 43 := by norm_num
            exact (pow_le_pow_left₀ hj_pos.le hj_lt41 2).trans_lt
              (h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide)))
          have h := Real.log_lt_log (pow_pos hj_pos 2) hp
          rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h; linarith
        have hllj41 : Real.log (Real.log j) < 31 / 10 := by
          have hp : (Real.log j) ^ 10 < (Real.exp 1) ^ 31 := by
            have h1 : (43 / 2 : ℝ) ^ 10 < (27182 / 10000 : ℝ) ^ 31 := by norm_num
            exact (pow_lt_pow_left₀ hlj41 (Real.log_pos hj_gt1).le (by decide)).trans
              (h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide)))
          have h := Real.log_lt_log (pow_pos (Real.log_pos hj_gt1) 10) hp
          rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h; linarith
        have hu_p := poolMaximum_upper upper n hj6
        have hX41 : utX n < ((41000 : ℝ) ^ 2 + 1) * (246 / 10) := by
          dsimp [utX]
          have h1 := mul_lt_mul_of_pos_left (show Real.log j + Real.log (Real.log j) < 246 / 10 by linarith) hj_pos
          nlinarith
        have hlogX41 : Real.log (utX n) < 49 / 2 := by
          have hp : (utX n) ^ 2 < (Real.exp 1) ^ 49 := by
            have h1 : (((41000 : ℝ) ^ 2 + 1) * (246 / 10)) ^ 2 < (27182 / 10000 : ℝ) ^ 49 := by norm_num
            exact (pow_lt_pow_left₀ hX41 hXpos.le (by decide)).trans
              (h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide)))
          have h := Real.log_lt_log (pow_pos hXpos 2) hp
          rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h; linarith
        have h12R : (12 : ℝ) ≤ (utLn n : ℝ) := by exact_mod_cast h12
        linarith
      have hLn_eq12 : utLn n = 12 := by
        by_contra hne12
        have h13 : 13 ≤ utLn n := by omega
        have h13R : (13 : ℝ) ≤ (utLn n : ℝ) := by exact_mod_cast h13
        have hn_le66 : (n : ℝ) ≤ 66000 := by exact_mod_cast (show n ≤ 66000 by omega)
        have hj_lt66 : j ≤ (66000 : ℝ) ^ 2 + 1 := by
          dsimp [j]; push_cast; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
        have hlj66 : Real.log j < 67 / 3 := by
          have hp : j ^ 3 < (Real.exp 1) ^ 67 := by
            have h1 : ((66000 : ℝ) ^ 2 + 1) ^ 3 < (27182 / 10000 : ℝ) ^ 67 := by norm_num
            exact (pow_le_pow_left₀ hj_pos.le hj_lt66 3).trans_lt
              (h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide)))
          have h := Real.log_lt_log (pow_pos hj_pos 3) hp
          rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h; linarith
        have hllj66 : Real.log (Real.log j) < 22 / 7 := by
          have hp : (Real.log j) ^ 7 < (Real.exp 1) ^ 22 := by
            have h1 : (67 / 3 : ℝ) ^ 7 < (27182 / 10000 : ℝ) ^ 22 := by norm_num
            exact (pow_lt_pow_left₀ hlj66 (Real.log_pos hj_gt1).le (by decide)).trans
              (h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide)))
          have h := Real.log_lt_log (pow_pos (Real.log_pos hj_gt1) 7) hp
          rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h; linarith
        have hu_p := poolMaximum_upper upper n hj6
        have hX66 : utX n < ((66000 : ℝ) ^ 2 + 1) * (535 / 21) := by
          dsimp [utX]
          have h1 := mul_lt_mul_of_pos_left (show Real.log j + Real.log (Real.log j) < 535 / 21 by linarith) hj_pos
          nlinarith
        have hp51 : (utX n) ^ 2 < (Real.exp 1) ^ 51 := by
          have h1 : (((66000 : ℝ) ^ 2 + 1) * (535 / 21)) ^ 2 < (27182 / 10000 : ℝ) ^ 51 := by norm_num
          exact (pow_lt_pow_left₀ hX66 hXpos.le (by decide)).trans
            (h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide)))
        have h := Real.log_lt_log (pow_pos hXpos 2) hp51
        rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h
        linarith
      have hs12 : utStepsMV n = 336 := by simp [utStepsMV, hLn_eq12]
      have hn41R : (41000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn41
      rw [hs12, hLn_eq12]; push_cast
      exact ⟨by linarith, by linarith⟩
    · have hn66' : 66000 ≤ n := by omega
      let v : ℝ := (n : ℝ) / 66000
      have hv_ge1 : 1 ≤ v := by
        have hnR : (66000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn66'
        dsimp [v]; linarith
      have hv_pos : 0 < v := by linarith
      have hlog_v_nn : 0 ≤ Real.log v := Real.log_nonneg hv_ge1
      let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
      have hj_pos : 0 < j := by dsimp [j]; positivity
      have hj_gt1 : 1 < j := by dsimp [j]; exact_mod_cast (show 1 < n * n + 1 by nlinarith)
      have hj_le_v2 : j ≤ 4356000001 * v ^ 2 := by
        have hn_eq : (n : ℝ) = 66000 * v := by dsimp [v]; ring
        have hj_eq : j = (n : ℝ) ^ 2 + 1 := by dsimp [j]; push_cast; ring
        rw [hj_eq, hn_eq]; have hv2 : 1 ≤ v ^ 2 := by nlinarith
        nlinarith
      have hlog_43 : Real.log 4356000001 < 67 / 3 := by
        have hp : (4356000001 : ℝ) ^ 3 < (Real.exp 1) ^ 67 := by
          have h1 : (4356000001 : ℝ) ^ 3 < (27182 / 10000 : ℝ) ^ 67 := by norm_num
          exact h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide))
        have h := Real.log_lt_log (by norm_num) hp
        rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h; linarith
      have hlogj_v : Real.log j < 67 / 3 + 2 * Real.log v := by
        have h1 := Real.log_le_log hj_pos hj_le_v2
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
        push_cast at h1; linarith
      have hlog67_lt : Real.log (67 / 3 : ℝ) < 22 / 7 := by
        have hp : (67 / 3 : ℝ) ^ 7 < (Real.exp 1) ^ 22 := by
          have h1 : (67 / 3 : ℝ) ^ 7 < (27182 / 10000 : ℝ) ^ 22 := by norm_num
          exact h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide))
        have h := Real.log_lt_log (by norm_num) hp
        rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h; linarith
      have hllj_v : Real.log (Real.log j) < 22 / 7 + Real.log v := by
        have h1 := Real.log_lt_log (Real.log_pos hj_gt1) hlogj_v
        have h67_eq : 67 / 3 + 2 * Real.log v = (67 / 3 : ℝ) * (1 + (6 / 67 : ℝ) * Real.log v) := by ring
        have h1p_pos : 0 < 1 + (6 / 67 : ℝ) * Real.log v := by linarith
        rw [h67_eq, Real.log_mul (by norm_num) h1p_pos.ne'] at h1
        have hsub := Real.log_le_sub_one_of_pos h1p_pos
        linarith
      have hsum_v : Real.log j + Real.log (Real.log j) < (535 / 21 : ℝ) * (1 + Real.log v / 8) := by
        linarith
      have hv_pow8 : (1 + Real.log v / 8) ^ 8 ≤ v := pow_one_add_log_div_le hv_ge1 8 (by decide)
      have hlog_1pv : Real.log (1 + Real.log v / 8) ≤ (1 / 8 : ℝ) * Real.log v := by
        have h1p8_pos : 0 < 1 + Real.log v / 8 := by linarith
        have h := Real.log_le_log (pow_pos h1p8_pos 8) hv_pow8
        rw [Real.log_pow] at h; push_cast at h; linarith
      have hu_p := poolMaximum_upper upper n (tail_prime_index_domains (by omega : 2001 ≤ n)).1
      have hX_v : utX n < (4356000001 * (535 / 21) : ℝ) * v ^ 2 * (1 + Real.log v / 8) := by
        dsimp [utX]
        have hp1 := mul_lt_mul_of_pos_left hsum_v hj_pos
        have hp2 := mul_le_mul_of_nonneg_right hj_le_v2 (show 0 ≤ (535 / 21 : ℝ) * (1 + Real.log v / 8) by linarith)
        linarith
      have hconst_v : Real.log (4356000001 * (535 / 21) : ℝ) < 51 / 2 := by
        have hp : (4356000001 * (535 / 21) : ℝ) ^ 2 < (Real.exp 1) ^ 51 := by
          have h1 : (4356000001 * (535 / 21) : ℝ) ^ 2 < (27182 / 10000 : ℝ) ^ 51 := by norm_num
          exact h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide))
        have h := Real.log_lt_log (by norm_num) hp
        rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h; linarith
      have hlogX_v : Real.log (utX n) < 51 / 2 + (17 / 8 : ℝ) * Real.log v := by
        have h1p8_pos : 0 < 1 + Real.log v / 8 := by linarith
        have h := Real.log_lt_log hXpos hX_v
        rw [Real.log_mul (by positivity) h1p8_pos.ne',
            Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
        push_cast at h; linarith
      have hLn_le_13 : (utLn n : ℝ) ≤ 13 * (1 + Real.log v / 2) := by linarith
      have hv_pow2 : (1 + Real.log v / 2) ^ 2 ≤ v := pow_one_add_log_div_le hv_ge1 2 (by decide)
      have hLn_sq66 : (utLn n : ℝ) ^ 2 ≤ (169 / 66000 : ℝ) * (n : ℝ) := by
        have h1 : (utLn n : ℝ) ^ 2 ≤ (13 * (1 + Real.log v / 2)) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hLn_le_13 2
        have h2 : (13 * (1 + Real.log v / 2)) ^ 2 = 169 * (1 + Real.log v / 2) ^ 2 := by ring
        have h3 : 169 * (1 + Real.log v / 2) ^ 2 ≤ 169 * v :=
          mul_le_mul_of_nonneg_left hv_pow2 (by norm_num : (0 : ℝ) ≤ 169)
        have h4 : 169 * v = (169 / 66000 : ℝ) * (n : ℝ) := by dsimp [v]; ring
        linarith
      have h12R : (12 : ℝ) ≤ (utLn n : ℝ) := by exact_mod_cast h12
      have hsteps_eq : (utStepsMV n : ℝ) = 2 * (utLn n : ℝ) ^ 2 + 4 * (utLn n : ℝ) := by
        have hnat : utStepsMV n = 2 * (utLn n * utLn n) + 4 * utLn n := by
          dsimp [utStepsMV]; zify [show 11 ≤ utLn n by omega]; ring
        have := congrArg (fun m : ℕ => (m : ℝ)) hnat
        push_cast at this; linarith
      have hlin_sq : (utLn n : ℝ) ≤ (1 / 12 : ℝ) * (utLn n : ℝ) ^ 2 := by nlinarith
      exact ⟨by linarith, by linarith⟩

/-- Envelope at threshold `n = 95,000` (`utLn n ≤ 13` below `95,000`, sharp quadratic step bound
above `95,000`) and universal total-stage packing bound `S_tot ≤ (2075 / 100000) * n`. -/
theorem ut_ln14_step_bounds
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n : ℕ} (hn : 35735 ≤ n) :
    (n ≤ 95000 → utLn n ≤ 13) ∧
    (95000 ≤ n → (utLn n : ℝ) ≤ (14 / 95000 : ℝ) * (n : ℝ) ∧
      (utLn n : ℝ) ^ 2 ≤ (196 / 95000 : ℝ) * (n : ℝ)) ∧
    (utStepsBoost n : ℝ) ≤ (110 / 95000 : ℝ) * (n : ℝ) ∧
    ((utSeedStages n + utStepsAP n + utStepsMV n + utStepsBoost n + utH0Max n + 10 + utWOrd n : ℕ) : ℝ) ≤
      (2075 / 100000 : ℝ) * (n : ℝ) := by
  obtain ⟨_, _, hLn11, hlogX_lo, _, _, _, _, _, _⟩ :=
    ut_sharp_scale_bounds rs lower sharp upper hn
  obtain ⟨_, h27_mv⟩ := ut_quadratic_step_bounds rs lower sharp upper hn
  have hexp1_gt : (27182 / 10000 : ℝ) < Real.exp 1 :=
    lt_trans (by norm_num) Real.exp_one_gt_d9
  have hXpos : 0 < utX n := by dsimp [utX]; exact_mod_cast (poolMaximum_prime n).pos
  have hj6 : 6 ≤ n * n + 1 := (tail_prime_index_domains (by omega : 2001 ≤ n)).1
  have hu_p := poolMaximum_upper upper n hj6
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hj_pos : 0 < j := by dsimp [j]; positivity
  have hj_gt1 : 1 < j := by dsimp [j]; exact_mod_cast (show 1 < n * n + 1 by nlinarith)
  have hle95 : n ≤ 95000 → utLn n ≤ 13 := by
    intro hn95
    by_contra hgt13
    have h14 : 14 ≤ utLn n := by omega
    have h14R : (14 : ℝ) ≤ (utLn n : ℝ) := by exact_mod_cast h14
    have hn95R : (n : ℝ) ≤ 95000 := by exact_mod_cast hn95
    have hj_lt : j ≤ (95000 : ℝ) ^ 2 + 1 := by
      dsimp [j]; push_cast; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    have hlj : Real.log j < 23 := by
      have hp : j ^ 3 < (Real.exp 1) ^ 69 := by
        have h1 : ((95000 : ℝ) ^ 2 + 1) ^ 3 < (27182 / 10000 : ℝ) ^ 69 := by norm_num
        exact (pow_le_pow_left₀ hj_pos.le hj_lt 3).trans_lt
          (h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide)))
      have h := Real.log_lt_log (pow_pos hj_pos 3) hp
      rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h; linarith
    have hllj : Real.log (Real.log j) < 22 / 7 := by
      have hp : (Real.log j) ^ 7 < (Real.exp 1) ^ 22 := by
        have h1 : (23 : ℝ) ^ 7 < (27182 / 10000 : ℝ) ^ 22 := by norm_num
        exact (pow_lt_pow_left₀ hlj (Real.log_pos hj_gt1).le (by decide)).trans
          (h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide)))
      have h := Real.log_lt_log (pow_pos (Real.log_pos hj_gt1) 7) hp
      rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h; linarith
    have hX95 : utX n < ((95000 : ℝ) ^ 2 + 1) * (183 / 7) := by
      dsimp [utX]
      have h1 := mul_lt_mul_of_pos_left (show Real.log j + Real.log (Real.log j) < 183 / 7 by linarith) hj_pos
      nlinarith
    have hp53 : (utX n) ^ 2 < (Real.exp 1) ^ 53 := by
      have h1 : (((95000 : ℝ) ^ 2 + 1) * (183 / 7)) ^ 2 < (27182 / 10000 : ℝ) ^ 53 := by norm_num
      exact (pow_lt_pow_left₀ hX95 hXpos.le (by decide)).trans
        (h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide)))
    have h := Real.log_lt_log (pow_pos hXpos 2) hp53
    rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h
    linarith
  have hge95 : 95000 ≤ n → (utLn n : ℝ) ≤ (14 / 95000 : ℝ) * (n : ℝ) ∧
      (utLn n : ℝ) ^ 2 ≤ (196 / 95000 : ℝ) * (n : ℝ) := by
    intro hn95
    let w : ℝ := (n : ℝ) / 95000
    have hw_ge1 : 1 ≤ w := by
      have hnR : (95000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn95
      dsimp [w]; linarith
    have hlog_w_nn : 0 ≤ Real.log w := Real.log_nonneg hw_ge1
    have hj_le_w2 : j ≤ 9025000001 * w ^ 2 := by
      have hn_eq : (n : ℝ) = 95000 * w := by dsimp [w]; ring
      have hj_eq : j = (n : ℝ) ^ 2 + 1 := by dsimp [j]; push_cast; ring
      rw [hj_eq, hn_eq]; have hw2 : 1 ≤ w ^ 2 := by nlinarith
      nlinarith
    have hlog_90 : Real.log 9025000001 < 23 := by
      have hp : (9025000001 : ℝ) ^ 3 < (Real.exp 1) ^ 69 := by
        have h1 : (9025000001 : ℝ) ^ 3 < (27182 / 10000 : ℝ) ^ 69 := by norm_num
        exact h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide))
      have h := Real.log_lt_log (by norm_num) hp
      rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h; linarith
    have hlogj_w : Real.log j < 23 + 2 * Real.log w := by
      have h1 := Real.log_le_log hj_pos hj_le_w2
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
      push_cast at h1; linarith
    have hlog23_lt : Real.log 23 < 22 / 7 := by
      have hp : (23 : ℝ) ^ 7 < (Real.exp 1) ^ 22 := by
        have h1 : (23 : ℝ) ^ 7 < (27182 / 10000 : ℝ) ^ 22 := by norm_num
        exact h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide))
      have h := Real.log_lt_log (by norm_num) hp
      rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h; linarith
    have hllj_w : Real.log (Real.log j) < 22 / 7 + Real.log w := by
      have h1 := Real.log_lt_log (Real.log_pos hj_gt1) hlogj_w
      have h23_eq : 23 + 2 * Real.log w = 23 * (1 + (2 / 23 : ℝ) * Real.log w) := by ring
      have h1p_pos : 0 < 1 + (2 / 23 : ℝ) * Real.log w := by linarith
      rw [h23_eq, Real.log_mul (by norm_num) h1p_pos.ne'] at h1
      have hsub := Real.log_le_sub_one_of_pos h1p_pos
      linarith
    have hsum_w : Real.log j + Real.log (Real.log j) < (183 / 7 : ℝ) * (1 + Real.log w / 8) := by
      linarith
    have hw_pow8 : (1 + Real.log w / 8) ^ 8 ≤ w := pow_one_add_log_div_le hw_ge1 8 (by decide)
    have hlog_1pw : Real.log (1 + Real.log w / 8) ≤ (1 / 8 : ℝ) * Real.log w := by
      have h1p8_pos : 0 < 1 + Real.log w / 8 := by linarith
      have h := Real.log_le_log (pow_pos h1p8_pos 8) hw_pow8
      rw [Real.log_pow] at h; push_cast at h; linarith
    have hX_w : utX n < (9025000001 * (183 / 7) : ℝ) * w ^ 2 * (1 + Real.log w / 8) := by
      dsimp [utX]
      have hp1 := mul_lt_mul_of_pos_left hsum_w hj_pos
      have hp2 := mul_le_mul_of_nonneg_right hj_le_w2 (show 0 ≤ (183 / 7 : ℝ) * (1 + Real.log w / 8) by linarith)
      linarith
    have hconst_w : Real.log (9025000001 * (183 / 7) : ℝ) < 53 / 2 := by
      have hp : (9025000001 * (183 / 7) : ℝ) ^ 2 < (Real.exp 1) ^ 53 := by
        have h1 : (9025000001 * (183 / 7) : ℝ) ^ 2 < (27182 / 10000 : ℝ) ^ 53 := by norm_num
        exact h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide))
      have h := Real.log_lt_log (by norm_num) hp
      rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h; linarith
    have hlogX_w : Real.log (utX n) < 53 / 2 + (17 / 8 : ℝ) * Real.log w := by
      have h1p8_pos : 0 < 1 + Real.log w / 8 := by linarith
      have h := Real.log_lt_log hXpos hX_w
      rw [Real.log_mul (by positivity) h1p8_pos.ne',
          Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
      push_cast at h; linarith
    have hLn_le_14 : (utLn n : ℝ) ≤ 14 * (1 + Real.log w / 2) := by linarith
    have hw_pow1 : 1 + Real.log w ≤ w := by
      simpa using pow_one_add_log_div_le hw_ge1 1 (by decide)
    have hw_pow2 : (1 + Real.log w / 2) ^ 2 ≤ w := pow_one_add_log_div_le hw_ge1 2 (by decide)
    have hlin : (utLn n : ℝ) ≤ (14 / 95000 : ℝ) * (n : ℝ) := by
      have h1 : 14 * (1 + Real.log w / 2) ≤ 14 * (1 + Real.log w) := by linarith
      have h2 : 14 * (1 + Real.log w) ≤ 14 * w := mul_le_mul_of_nonneg_left hw_pow1 (by norm_num)
      have h3 : 14 * w = (14 / 95000 : ℝ) * (n : ℝ) := by dsimp [w]; ring
      linarith
    have hsq : (utLn n : ℝ) ^ 2 ≤ (196 / 95000 : ℝ) * (n : ℝ) := by
      have h1 : (utLn n : ℝ) ^ 2 ≤ (14 * (1 + Real.log w / 2)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hLn_le_14 2
      have h2 : (14 * (1 + Real.log w / 2)) ^ 2 = 196 * (1 + Real.log w / 2) ^ 2 := by ring
      have h3 : 196 * (1 + Real.log w / 2) ^ 2 ≤ 196 * w := mul_le_mul_of_nonneg_left hw_pow2 (by norm_num)
      have h4 : 196 * w = (196 / 95000 : ℝ) * (n : ℝ) := by dsimp [w]; ring
      linarith
    exact ⟨hlin, hsq⟩
  have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hWOrd_le : (utWOrd n : ℝ) ≤ (n : ℝ) / 430 + 12 := by
    have hdiv : utWOrd n * 430 ≤ n + 12 * 430 := by dsimp [utWOrd]; omega
    have hdivR : (utWOrd n : ℝ) * 430 ≤ (n : ℝ) + 12 * 430 := by exact_mod_cast hdiv
    linarith
  by_cases hLn13 : utLn n ≤ 13
  · have hb0 : utStepsBoost n = 0 := by simp [utStepsBoost, hLn13]
    refine ⟨hle95, hge95, ?_, ?_⟩
    · rw [hb0]; push_cast; positivity
    · have hsum_eq : (utSeedStages n + utStepsAP n + utStepsMV n + utStepsBoost n + utH0Max n + 10 + utWOrd n : ℕ) =
          30 * utLn n + utStepsMV n + utWOrd n + 29 := by
        rw [hb0]; dsimp [utSeedStages, utStepsAP, utStepsAP1, utStepsAP2, utH0Max]; omega
      rw [hsum_eq]; push_cast; linarith
  · have h14 : 14 ≤ utLn n := by omega
    have hn95 : 95000 ≤ n := by
      by_contra hlt; exact hLn13 (hle95 (by omega))
    obtain ⟨hlin95, hsq95⟩ := hge95 hn95
    have hn95R : (95000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn95
    have hboost_le : (utStepsBoost n : ℝ) ≤ (3 / 10 : ℝ) * (utLn n : ℝ) ^ 2 + 3 * (utLn n : ℝ) + 17 / 2 := by
      have h1 : utStepsBoost n * 30 ≤ utH0Max n * utH0Max n + 30 := by
        dsimp [utStepsBoost]; rw [if_neg hLn13]; omega
      have h1R : (utStepsBoost n : ℝ) * 30 ≤ ((utH0Max n : ℝ)) ^ 2 + 30 := by
        have := (show (utStepsBoost n * 30 : ℝ) ≤ ((utH0Max n * utH0Max n + 30 : ℕ) : ℝ) by exact_mod_cast h1)
        push_cast at this; nlinarith
      have hH_eq : (utH0Max n : ℝ) = 3 * ((utLn n : ℝ) + 5) := by dsimp [utH0Max]; push_cast; ring
      rw [hH_eq] at h1R; nlinarith
    have hboost_n : (utStepsBoost n : ℝ) ≤ (110 / 95000 : ℝ) * (n : ℝ) := by linarith
    have hmv_eq : (utStepsMV n : ℝ) ≤ 2 * (utLn n : ℝ) ^ 2 + 4 * (utLn n : ℝ) := by
      have hnat : utStepsMV n = 2 * (utLn n * utLn n) + 4 * utLn n := by
        dsimp [utStepsMV]; zify [show 11 ≤ utLn n by omega]; ring
      have := congrArg (fun m : ℕ => (m : ℝ)) hnat
      push_cast at this; linarith
    refine ⟨hle95, hge95, hboost_n, ?_⟩
    have hsum_eq : (utSeedStages n + utStepsAP n + utStepsMV n + utStepsBoost n + utH0Max n + 10 + utWOrd n : ℕ) =
        30 * utLn n + utStepsMV n + utStepsBoost n + utWOrd n + 29 := by
      dsimp [utSeedStages, utStepsAP, utStepsAP1, utStepsAP2, utH0Max]; omega
    rw [hsum_eq]; push_cast; linarith

/-- Refined small-`n` logarithmic caps (`n ≤ 42,000 → utLn n ≤ 11`, `n ≤ 68,000 → utLn n ≤ 12`)
and global linear cap `(utLn n : ℝ) ≤ (31 / 100000) * n` across all `n ≥ 35,735`. -/
theorem utLn_small_and_linear_bounds
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n : ℕ} (hn : 35735 ≤ n) :
    (n ≤ 42000 → utLn n ≤ 11) ∧
    (n ≤ 68000 → utLn n ≤ 12) ∧
    (utLn n : ℝ) ≤ (31 / 100000 : ℝ) * (n : ℝ) := by
  obtain ⟨hle95, hge95, _, _⟩ := ut_ln14_step_bounds rs lower sharp upper hn
  have hlog24 := (ut_sharp_scale_bounds rs lower sharp upper hn).1
  have hexp1_gt : (27182 / 10000 : ℝ) < Real.exp 1 :=
    lt_trans (by norm_num) Real.exp_one_gt_d9
  have hXpos : 0 < utX n := by dsimp [utX]; exact_mod_cast (poolMaximum_prime n).pos
  have hj6 : 6 ≤ n * n + 1 := (tail_prime_index_domains (by omega : 2001 ≤ n)).1
  have hu_p := poolMaximum_upper upper n hj6
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hj_pos : 0 < j := by dsimp [j]; positivity
  have hj_gt1 : 1 < j := by dsimp [j]; exact_mod_cast (show 1 < n * n + 1 by nlinarith)
  have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hle42 : n ≤ 42000 → utLn n ≤ 11 := by
    intro hn42
    by_contra hgt11
    have h49 : (49 : ℝ) ≤ 2 * Real.log (utX n) := by
      have h1 : 49 ≤ utL2X n := by dsimp [utLn] at hgt11; omega
      have h2 : (49 : ℝ) ≤ (utL2X n : ℝ) := by exact_mod_cast h1
      have h3 : (utL2X n : ℝ) ≤ 2 * Real.log (utX n) := by
        dsimp [utL2X]; exact Nat.floor_le (by linarith)
      linarith
    have hn42R : (n : ℝ) ≤ 42000 := by exact_mod_cast hn42
    have hj_lt : j ≤ (42000 : ℝ) ^ 2 + 1 := by
      dsimp [j]; push_cast; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    have hlj : Real.log j < 64 / 3 := by
      have hp : j ^ 3 < (Real.exp 1) ^ 64 := by
        have h1 : ((42000 : ℝ) ^ 2 + 1) ^ 3 < (27182 / 10000 : ℝ) ^ 64 := by norm_num
        exact (pow_le_pow_left₀ hj_pos.le hj_lt 3).trans_lt
          (h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide)))
      have h := Real.log_lt_log (pow_pos hj_pos 3) hp
      rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h; linarith
    have hllj : Real.log (Real.log j) < 22 / 7 := by
      have hp : (Real.log j) ^ 7 < (Real.exp 1) ^ 22 := by
        have h1 : (64 / 3 : ℝ) ^ 7 < (27182 / 10000 : ℝ) ^ 22 := by norm_num
        exact (pow_lt_pow_left₀ hlj (Real.log_pos hj_gt1).le (by decide)).trans
          (h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide)))
      have h := Real.log_lt_log (pow_pos (Real.log_pos hj_gt1) 7) hp
      rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h; linarith
    have hX42 : utX n < ((42000 : ℝ) ^ 2 + 1) * (514 / 21) := by
      dsimp [utX]
      have h1 := mul_lt_mul_of_pos_left
        (show Real.log j + Real.log (Real.log j) < 514 / 21 by linarith) hj_pos
      nlinarith
    have hp49 : (utX n) ^ 2 < (Real.exp 1) ^ 49 := by
      have h1 : (((42000 : ℝ) ^ 2 + 1) * (514 / 21)) ^ 2 < (27182 / 10000 : ℝ) ^ 49 := by norm_num
      exact (pow_lt_pow_left₀ hX42 hXpos.le (by decide)).trans
        (h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide)))
    have h := Real.log_lt_log (pow_pos hXpos 2) hp49
    rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h; linarith
  have hle68 : n ≤ 68000 → utLn n ≤ 12 := by
    intro hn68
    by_contra hgt12
    have h51 : (51 : ℝ) ≤ 2 * Real.log (utX n) := by
      have h1 : 51 ≤ utL2X n := by dsimp [utLn] at hgt12; omega
      have h2 : (51 : ℝ) ≤ (utL2X n : ℝ) := by exact_mod_cast h1
      have h3 : (utL2X n : ℝ) ≤ 2 * Real.log (utX n) := by
        dsimp [utL2X]; exact Nat.floor_le (by linarith)
      linarith
    have hn68R : (n : ℝ) ≤ 68000 := by exact_mod_cast hn68
    have hj_lt : j ≤ (68000 : ℝ) ^ 2 + 1 := by
      dsimp [j]; push_cast; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    have hlj : Real.log j < 67 / 3 := by
      have hp : j ^ 3 < (Real.exp 1) ^ 67 := by
        have h1 : ((68000 : ℝ) ^ 2 + 1) ^ 3 < (27182 / 10000 : ℝ) ^ 67 := by norm_num
        exact (pow_le_pow_left₀ hj_pos.le hj_lt 3).trans_lt
          (h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide)))
      have h := Real.log_lt_log (pow_pos hj_pos 3) hp
      rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h; linarith
    have hllj : Real.log (Real.log j) < 22 / 7 := by
      have hp : (Real.log j) ^ 7 < (Real.exp 1) ^ 22 := by
        have h1 : (67 / 3 : ℝ) ^ 7 < (27182 / 10000 : ℝ) ^ 22 := by norm_num
        exact (pow_lt_pow_left₀ hlj (Real.log_pos hj_gt1).le (by decide)).trans
          (h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide)))
      have h := Real.log_lt_log (pow_pos (Real.log_pos hj_gt1) 7) hp
      rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h; linarith
    have hX68 : utX n < ((68000 : ℝ) ^ 2 + 1) * (535 / 21) := by
      dsimp [utX]
      have h1 := mul_lt_mul_of_pos_left
        (show Real.log j + Real.log (Real.log j) < 535 / 21 by linarith) hj_pos
      nlinarith
    have hp51 : (utX n) ^ 2 < (Real.exp 1) ^ 51 := by
      have h1 : (((68000 : ℝ) ^ 2 + 1) * (535 / 21)) ^ 2 < (27182 / 10000 : ℝ) ^ 51 := by norm_num
      exact (pow_lt_pow_left₀ hX68 hXpos.le (by decide)).trans
        (h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide)))
    have h := Real.log_lt_log (pow_pos hXpos 2) hp51
    rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h; linarith
  refine ⟨hle42, hle68, ?_⟩
  by_cases hn42 : n ≤ 42000
  · have h1 : (utLn n : ℝ) ≤ 11 := by exact_mod_cast (hle42 hn42)
    linarith
  · by_cases hn68 : n ≤ 68000
    · have hn42' : (42001 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 42001 ≤ n by omega)
      have h1 : (utLn n : ℝ) ≤ 12 := by exact_mod_cast (hle68 hn68)
      linarith
    · by_cases hn95 : n ≤ 95000
      · have hn68' : (68001 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 68001 ≤ n by omega)
        have h1 : (utLn n : ℝ) ≤ 13 := by exact_mod_cast (hle95 hn95)
        linarith
      · have h1 := (hge95 (by omega)).1
        linarith

/-! ## Section 5: Concrete Scalar Gate Lemmas (`n ≥ 35,735`) -/

/-- For any `g` divisible by `6`, `φ(g) ≤ g / 3` (and if `0 < g`, `2 ≤ φ(g)`). -/
theorem ut_totient_six_dvd_bounds {g : ℕ} (hg : 0 < g) (hdvd : 6 ∣ g) :
    2 ≤ Nat.totient g ∧ 3 * Nat.totient g ≤ g := by
  obtain ⟨k, rfl⟩ := hdvd
  have hk : 0 < k := by omega
  let S := (Finset.range (6 * k)).filter (Nat.Coprime (6 * k))
  have htot : Nat.totient (6 * k) = S.card := Nat.totient_eq_card_coprime (6 * k)
  rw [htot]
  have h2 : 2 ≤ S.card := by
    have hsub : ({1, 6 * k - 1} : Finset ℕ) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp [S, Finset.mem_filter, Finset.mem_range, show 1 < 6 * k by omega]
      · rw [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        rw [Nat.Coprime]
        apply Nat.eq_one_of_dvd_one
        have hd1 : Nat.gcd (6 * k) (6 * k - 1) ∣ 6 * k := Nat.gcd_dvd_left _ _
        have hd2 : Nat.gcd (6 * k) (6 * k - 1) ∣ 6 * k - 1 := Nat.gcd_dvd_right _ _
        have hd_sub := Nat.dvd_sub hd1 hd2
        simpa [show 6 * k - (6 * k - 1) = 1 by omega] using hd_sub
    have hne : (1 : ℕ) ≠ 6 * k - 1 := by omega
    have hc := Finset.card_le_card hsub
    rwa [Finset.card_pair hne] at hc
  have h3 : 3 * S.card ≤ 6 * k := by
    let f : ℕ → ℕ × ℕ := fun x => (x / 6, x % 6)
    have hmaps : ∀ x ∈ S, f x ∈ Finset.range k ×ˢ ({1, 5} : Finset ℕ) := by
      intro x hx
      obtain ⟨hxr, hcop⟩ := Finset.mem_filter.mp hx
      have hxlt : x < 6 * k := Finset.mem_range.mp hxr
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      dsimp [f]
      have hdiv6 := Nat.div_add_mod x 6
      have hmod6 : x % 6 < 6 := Nat.mod_lt x (by decide)
      refine ⟨by omega, ?_⟩
      by_contra hnot
      have hcases : x % 6 = 0 ∨ x % 6 = 2 ∨ x % 6 = 3 ∨ x % 6 = 4 := by omega
      rcases hcases with h0 | h2' | h3' | h4
      · have hd2_x : 2 ∣ x := ⟨x / 2, by omega⟩
        have hd2_6k : 2 ∣ 6 * k := ⟨3 * k, by ring⟩
        have hd := Nat.dvd_gcd hd2_6k hd2_x
        rw [hcop.gcd_eq_one] at hd; omega
      · have hd2_x : 2 ∣ x := ⟨x / 2, by omega⟩
        have hd2_6k : 2 ∣ 6 * k := ⟨3 * k, by ring⟩
        have hd := Nat.dvd_gcd hd2_6k hd2_x
        rw [hcop.gcd_eq_one] at hd; omega
      · have hd3_x : 3 ∣ x := ⟨x / 3, by omega⟩
        have hd3_6k : 3 ∣ 6 * k := ⟨2 * k, by ring⟩
        have hd := Nat.dvd_gcd hd3_6k hd3_x
        rw [hcop.gcd_eq_one] at hd; omega
      · have hd2_x : 2 ∣ x := ⟨x / 2, by omega⟩
        have hd2_6k : 2 ∣ 6 * k := ⟨3 * k, by ring⟩
        have hd := Nat.dvd_gcd hd2_6k hd2_x
        rw [hcop.gcd_eq_one] at hd; omega
    have hinj : Set.InjOn f ↑S := by
      intro a _ b _ hab
      obtain ⟨hq, hr⟩ := Prod.mk.inj hab
      have ha := Nat.div_add_mod a 6
      have hb := Nat.div_add_mod b 6
      omega
    have hcard_le := Finset.card_le_card_of_injOn f hmaps hinj
    have hprod_card : (Finset.range k ×ˢ ({1, 5} : Finset ℕ)).card = 2 * k := by
      rw [Finset.card_product, Finset.card_range, Finset.card_pair (by decide)]; ring
    omega
  exact ⟨h2, h3⟩

/-- `Pool 1` (`(0.068 * X, 0.323 * X]`) and `Pool 2` (`(0.581 * X, 0.836 * X]`) odd-prime supply
(`≥ (509 / 2000) * utY n`) for all `n ≥ 35,735`. -/
theorem ut_pool_card_lowers
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n : ℕ} (hn : 35735 ≤ n) :
    (509 / 2000 : ℝ) * utY n ≤ (apInterval (utPool1Lo n) (utPool1Hi n) 2 1).card ∧
    (509 / 2000 : ℝ) * utY n ≤ (apInterval (utPool2Lo n) (utPool2Hi n) 2 1).card := by
  obtain ⟨_, hX_283, _, _, _⟩ := poolMaximum_bounds_ge_35735 sharp upper hn
  have hX : (283 * 10 ^ 8 : ℝ) ≤ utX n := by dsimp [utX]; exact hX_283.le
  have hlog : 0 < Real.log (utX n) := Real.log_pos (by linarith)
  have h1 := apInterval_mod_two_card_lower_ge_1e9 bmor imp
    (b := utPool1Lo n) (c := utPool1Hi n) (X := utX n)
    (by dsimp [utPool1Lo]; linarith) (by dsimp [utPool1Lo, utPool1Hi]; linarith)
    (by dsimp [utPool1Hi]; linarith)
  have h2 := apInterval_mod_two_card_lower_ge_9e9 bmor imp
    (b := utPool2Lo n) (c := utPool2Hi n) (X := utX n)
    (by dsimp [utPool2Lo]; linarith) (by dsimp [utPool2Lo, utPool2Hi]; linarith)
    (by dsimp [utPool2Hi]; linarith)
  have h1' : (509 / 2000 : ℝ) * utY n ≤
      ((utPool1Hi n - utPool1Lo n) - (utPool1Lo n + utPool1Hi n) / 7600) / Real.log (utX n) := by
    dsimp [utY, utPool1Lo, utPool1Hi]
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by linarith) hlog.le
  have h2' : (509 / 2000 : ℝ) * utY n ≤
      ((utPool2Hi n - utPool2Lo n) - (utPool2Lo n + utPool2Hi n) / 22000) / Real.log (utX n) := by
    dsimp [utY, utPool2Lo, utPool2Hi]
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by linarith) hlog.le
  exact ⟨h1'.trans h1, h2'.trans h2⟩

/-- Scalar gates for Seed extraction (`ap_interval_stage_from_source_budget`) on `Pool 2`:
extracting `Q_cand = (utSeedStages n + 1) * utQ n` pairs of common gap `g` (`6 ∣ g`, `g ≤ utSeedCap n`). -/
theorem ut_seed_scalar_gates
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n : ℕ} (hn : 35735 ≤ n) :
    let X := utX n
    let Y := utY n
    let R := (utSeedCap n : ℝ)
    let M := (509 / 2000 : ℝ) * Y
    let Q_cand := (utSeedStages n + 4) * utQ n
    let width := (6 : ℝ) * ((105 / 100 : ℝ) * M * R / (2 * X) - 1 / 2)
    0 ≤ (1 / (2 * ((255 / 1000 : ℝ) + 1 / (1000 : ℝ))) - (105 / 100 : ℝ)) ∧
    R ≤ X / 1000 ∧
    0 < width ∧
    2 * (Q_cand : ℝ) * 2 * X ≤
      (1 / (2 * ((255 / 1000 : ℝ) + 1 / (1000 : ℝ))) - (105 / 100 : ℝ)) * M ^ 2 * 6 ∧
    2 * Q_cand < Nat.ceil M := by
  obtain ⟨hlog24, _, hLn11, _, hlog_hi, hY_gt, _, _, hLn_lin, _⟩ :=
    ut_sharp_scale_bounds rs lower sharp upper hn
  obtain ⟨hle42, hle68, _⟩ := utLn_small_and_linear_bounds rs lower sharp upper hn
  obtain ⟨hle95, hge95, _, _⟩ := ut_ln14_step_bounds rs lower sharp upper hn
  obtain ⟨hX_sq, hX_283, _, _, _⟩ := poolMaximum_bounds_ge_35735 sharp upper hn
  have hX : (283 * 10 ^ 8 : ℝ) ≤ utX n := by dsimp [utX]; exact hX_283.le
  have hX_pos : 0 < utX n := by linarith
  have hlog_pos : 0 < Real.log (utX n) := by linarith
  have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hLnR : (11 : ℝ) ≤ (utLn n : ℝ) := by exact_mod_cast hLn11
  have hY_pos : 0 < utY n := by nlinarith
  dsimp only
  have hR_le : (utSeedCap n : ℝ) ≤ utX n / 1000 := by
    have hcap : (utSeedCap n : ℝ) = 6 * ((utLn n : ℝ) + 5) := by dsimp [utSeedCap]; push_cast; ring
    have hn_le_X : (n : ℝ) ≤ utX n / 700000 := by
      dsimp [utX]; nlinarith
    rw [hcap]; linarith
  have hYX : utY n * Real.log (utX n) = utX n := div_mul_cancel₀ _ hlog_pos.ne'
  have hw_pos : 0 < (6 : ℝ) * ((105 / 100 : ℝ) * ((509 / 2000 : ℝ) * utY n) * (utSeedCap n : ℝ) / (2 * utX n) - 1 / 2) := by
    have hcap : (utSeedCap n : ℝ) = 6 * ((utLn n : ℝ) + 5) := by dsimp [utSeedCap]; push_cast; ring
    have hnum : utX n < (105 / 100 : ℝ) * ((509 / 2000 : ℝ) * utY n) * (utSeedCap n : ℝ) := by
      rw [← hYX, hcap]
      have hcoef : Real.log (utX n) < (105 / 100 : ℝ) * (509 / 2000 : ℝ) * (6 * ((utLn n : ℝ) + 5)) := by linarith
      have hm := mul_lt_mul_of_pos_right hcoef hY_pos
      linarith
    have hdiv : (1 / 2 : ℝ) < (105 / 100 : ℝ) * ((509 / 2000 : ℝ) * utY n) * (utSeedCap n : ℝ) / (2 * utX n) := by
      rw [lt_div_iff₀ (by linarith)]
      linarith
    linarith
  have hQcand_eq : (((utSeedStages n + 4) * utQ n : ℕ) : ℝ) =
      ((utLn n : ℝ) + 8) * (6 * (n : ℝ) + 4) := by
    dsimp [utSeedStages, utQ]; push_cast; ring
  have hbt5 : 2 * (((utSeedStages n + 4) * utQ n : ℕ) : ℝ) * 2 * utX n ≤
      (1 / (2 * ((255 / 1000 : ℝ) + 1 / (1000 : ℝ))) - (105 / 100 : ℝ)) *
        ((509 / 2000 : ℝ) * utY n) ^ 2 * 6 := by
    have hprod_Ln : ((utLn n : ℝ) + 8) * Real.log (utX n) ≤ (131 / 10000 : ℝ) * (n : ℝ) := by
      by_cases hn42 : n ≤ 42000
      · have h1 : (utLn n : ℝ) ≤ 11 := by exact_mod_cast (hle42 hn42)
        have h2 : Real.log (utX n) ≤ 49 / 2 := by linarith
        nlinarith
      · by_cases hn68 : n ≤ 68000
        · have hn42' : (42001 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 42001 ≤ n by omega)
          have h1 : (utLn n : ℝ) ≤ 12 := by exact_mod_cast (hle68 hn68)
          have h2 : Real.log (utX n) ≤ 51 / 2 := by linarith
          nlinarith
        · by_cases hn95 : n ≤ 95000
          · have hn68' : (68001 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 68001 ≤ n by omega)
            have h1 : (utLn n : ℝ) ≤ 13 := by exact_mod_cast (hle95 hn95)
            have h2 : Real.log (utX n) ≤ 53 / 2 := by linarith
            nlinarith
          · obtain ⟨_, hsq95⟩ := hge95 (by omega)
            have hLn8 : (utLn n : ℝ) + 8 ≤ (19 / 11 : ℝ) * (utLn n : ℝ) := by linarith
            have hlog_Ln : Real.log (utX n) ≤ (49 / 22 : ℝ) * (utLn n : ℝ) := by linarith
            have h1 : ((utLn n : ℝ) + 8) * Real.log (utX n) ≤
                ((19 / 11 : ℝ) * (utLn n : ℝ)) * ((49 / 22 : ℝ) * (utLn n : ℝ)) :=
              mul_le_mul hLn8 hlog_Ln hlog_pos.le (by positivity)
            nlinarith
    have h6n4 : 6 * (n : ℝ) + 4 ≤ (6001 / 1000 : ℝ) * (n : ℝ) := by linarith
    have hprod_n2 : (((utLn n : ℝ) + 8) * Real.log (utX n)) * (6 * (n : ℝ) + 4) ≤
        ((131 / 10000 : ℝ) * (n : ℝ)) * ((6001 / 1000 : ℝ) * (n : ℝ)) :=
      mul_le_mul hprod_Ln h6n4 (by positivity) (by positivity)
    have hlhs_le : 2 * (((utSeedStages n + 4) * utQ n : ℕ) : ℝ) * 2 * utX n ≤
        (315 / 1000 : ℝ) * (n : ℝ) ^ 2 * utY n := by
      have hrew : 2 * (((utSeedStages n + 4) * utQ n : ℕ) : ℝ) * 2 * utX n =
          (4 * ((((utLn n : ℝ) + 8) * Real.log (utX n)) * (6 * (n : ℝ) + 4))) * utY n := by
        rw [hQcand_eq]
        calc 2 * (((utLn n : ℝ) + 8) * (6 * (n : ℝ) + 4)) * 2 * utX n
            = 2 * (((utLn n : ℝ) + 8) * (6 * (n : ℝ) + 4)) * 2 * (utY n * Real.log (utX n)) := by rw [hYX]
          _ = (4 * ((((utLn n : ℝ) + 8) * Real.log (utX n)) * (6 * (n : ℝ) + 4))) * utY n := by ring
      rw [hrew]
      have hnum_le : 4 * ((((utLn n : ℝ) + 8) * Real.log (utX n)) * (6 * (n : ℝ) + 4)) ≤
          (315 / 1000 : ℝ) * (n : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right hnum_le hY_pos.le
    have heps : (90 / 100 : ℝ) ≤ 1 / (2 * ((255 / 1000 : ℝ) + 1 / (1000 : ℝ))) - (105 / 100 : ℝ) := by norm_num
    have hrhs_ge : (315 / 1000 : ℝ) * (n : ℝ) ^ 2 * utY n ≤
        (90 / 100 : ℝ) * ((509 / 2000 : ℝ) * utY n) ^ 2 * 6 := by
      have hY2 : (925 / 1000 : ℝ) * (n : ℝ) ^ 2 * utY n ≤ (utY n) ^ 2 := by
        have hm := mul_le_mul_of_nonneg_right hY_gt.le hY_pos.le
        linarith
      nlinarith
    have h_rhs_mono : (90 / 100 : ℝ) * ((509 / 2000 : ℝ) * utY n) ^ 2 * 6 ≤
        (1 / (2 * ((255 / 1000 : ℝ) + 1 / (1000 : ℝ))) - (105 / 100 : ℝ)) *
          ((509 / 2000 : ℝ) * utY n) ^ 2 * 6 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right heps (sq_nonneg _)) (by norm_num)
    exact hlhs_le.trans (hrhs_ge.trans h_rhs_mono)
  have h2Q_lt : 2 * ((utSeedStages n + 4) * utQ n) < Nat.ceil ((509 / 2000 : ℝ) * utY n) := by
    have hLn8_n : (utLn n : ℝ) + 8 ≤ (6 / 10000 : ℝ) * (n : ℝ) := by linarith
    have h6n4 : 6 * (n : ℝ) + 4 ≤ (6001 / 1000 : ℝ) * (n : ℝ) := by linarith
    have hprod := mul_le_mul hLn8_n h6n4 (by positivity) (by positivity)
    have hreal : ((2 * ((utSeedStages n + 4) * utQ n) : ℕ) : ℝ) < (509 / 2000 : ℝ) * utY n := by
      push_cast at hQcand_eq ⊢; nlinarith
    exact_mod_cast hreal.trans_le (Nat.le_ceil _)
  exact ⟨by norm_num, hR_le, hw_pos, hbt5, h2Q_lt⟩

/-- Scalar gates for the first `AP` subphase `AP_1` (`ap_narrow_linear_phase_from_scalar`) on `Pool 1`
with `c = 255/1000, r = g / 3, L = 200, η = 180/100, Ma = 509/2000 * Y, Mf = 222/1000 * Y`,
`initialRadius = utSeedStages n * g`, `target = 15 * utLn n * g`, `z = 2`. -/
theorem ut_ap1_scalar_gates
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n g : ℕ} (hn : 35735 ≤ n) (hg_pos : 0 < g) (hg_dvd : 6 ∣ g) (hg_le : g ≤ utSeedCap n) :
    let X := utX n
    let Y := utY n
    let r : ℝ := (g : ℝ) / 3
    let L : ℝ := 200
    let η : ℝ := 180 / 100
    let Ma : ℝ := (509 / 2000 : ℝ) * Y
    let Mf : ℝ := (222 / 1000 : ℝ) * Y
    let R0 : ℕ := utSeedStages n * g
    let target : ℝ := (15 : ℝ) * (utLn n : ℝ) * (g : ℝ)
    let steps := utStepsAP1 n
    let Q := utQ n
    0 ≤ 1 / (2 * ((255 / 1000 : ℝ) + 1 / L)) - η ∧
    2 * Q * steps < Nat.ceil Ma ∧
    Mf ≤ Ma - 2 * (Q : ℝ) * (steps : ℝ) ∧
    2 * ((2 * Q : ℕ) : ℝ) * r * X ≤ (1 / (2 * ((255 / 1000 : ℝ) + 1 / L)) - η) * Mf ^ 2 * (g : ℝ) ∧
    0 < (R0 : ℝ) - r * X / (2 * η * Mf) ∧
    target ≤ X / L - r * X / (2 * η * Mf) ∧
    Real.log (target / ((R0 : ℝ) - r * X / (2 * η * Mf))) ≤
      (η * (g : ℝ) / (r * X)) * ((steps : ℝ) * Ma - (Q : ℝ) * (steps : ℝ) * ((steps : ℝ) - 1)) /
        (1 + (η * (g : ℝ) / (r * X)) * Ma) := by
  obtain ⟨hlog24, _, hLn11, hlog_lo, hlog_hi, hY_gt, _, _, hLn_lin, hLn_sq⟩ :=
    ut_sharp_scale_bounds rs lower sharp upper hn
  have hlog_ub_n := ut_logX_lt_linear rs lower sharp upper hn
  obtain ⟨hX_sq, hX_283, _, _, _⟩ := poolMaximum_bounds_ge_35735 sharp upper hn
  have hX : (283 * 10 ^ 8 : ℝ) ≤ utX n := by dsimp [utX]; exact hX_283.le
  have hX_pos : 0 < utX n := by linarith
  have hlog_pos : 0 < Real.log (utX n) := by linarith
  have hYX : utY n * Real.log (utX n) = utX n := div_mul_cancel₀ _ hlog_pos.ne'
  have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hLnR : (11 : ℝ) ≤ (utLn n : ℝ) := by exact_mod_cast hLn11
  have hY_pos : 0 < utY n := by nlinarith
  have hg6 : 6 ≤ g := by obtain ⟨k, rfl⟩ := hg_dvd; omega
  have hgR : (6 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg6
  have hg_posR : (0 : ℝ) < (g : ℝ) := by linarith
  have hg_ub : (g : ℝ) ≤ 6 * ((utLn n : ℝ) + 5) := by
    have : (g : ℝ) ≤ (utSeedCap n : ℝ) := by exact_mod_cast hg_le
    dsimp [utSeedCap] at this; push_cast at this; linarith
  dsimp only
  have heps : (123 / 1000 : ℝ) ≤ 1 / (2 * ((255 / 1000 : ℝ) + 1 / (200 : ℝ))) - (180 / 100 : ℝ) := by norm_num
  have h2Qsteps : 2 * (utQ n : ℝ) * (utStepsAP1 n : ℝ) ≤ (32 / 1000 : ℝ) * utY n := by
    have h1 : 2 * (utQ n : ℝ) * (utStepsAP1 n : ℝ) = 14 * (utLn n : ℝ) * (6 * (n : ℝ) + 4) := by
      dsimp [utQ, utStepsAP1]; push_cast; ring
    have h6n4 : 6 * (n : ℝ) + 4 ≤ (6001 / 1000 : ℝ) * (n : ℝ) := by linarith
    have hp := mul_le_mul hLn_lin h6n4 (by positivity) (by positivity)
    rw [h1]; nlinarith
  have hfloor : (222 / 1000 : ℝ) * utY n ≤ (509 / 2000 : ℝ) * utY n - 2 * (utQ n : ℝ) * (utStepsAP1 n : ℝ) := by
    linarith
  have hstock : 2 * utQ n * utStepsAP1 n < Nat.ceil ((509 / 2000 : ℝ) * utY n) := by
    have hreal : ((2 * utQ n * utStepsAP1 n : ℕ) : ℝ) < (509 / 2000 : ℝ) * utY n := by
      push_cast; linarith
    exact_mod_cast hreal.trans_le (Nat.le_ceil _)
  have hpair : 2 * ((2 * utQ n : ℕ) : ℝ) * ((g : ℝ) / 3) * utX n ≤
      (1 / (2 * ((255 / 1000 : ℝ) + 1 / (200 : ℝ))) - (180 / 100 : ℝ)) *
        ((222 / 1000 : ℝ) * utY n) ^ 2 * (g : ℝ) := by
    have h1 : (4 / 3 : ℝ) * (utQ n : ℝ) * utX n ≤
        (123 / 1000 : ℝ) * ((222 / 1000 : ℝ) * utY n) ^ 2 := by
      have hQ_eq : (utQ n : ℝ) = 6 * (n : ℝ) + 4 := by dsimp [utQ]; push_cast; ring
      have hX_ub : utX n < (68 / 100000 : ℝ) * (n : ℝ) * utY n := by
        rw [← hYX]
        have hm := mul_lt_mul_of_pos_right hlog_ub_n hY_pos
        linarith
      have hQX : (utQ n : ℝ) * utX n ≤ ((6001 / 1000 : ℝ) * (n : ℝ)) * ((68 / 100000 : ℝ) * (n : ℝ) * utY n) := by
        rw [hQ_eq]; exact mul_le_mul (by linarith) hX_ub.le hX_pos.le (by positivity)
      have hY2 : (925 / 1000 : ℝ) * (n : ℝ) ^ 2 * utY n ≤ (utY n) ^ 2 := by
        have hm := mul_le_mul_of_nonneg_right hY_gt.le hY_pos.le
        linarith
      nlinarith
    have h2 : 2 * ((2 * utQ n : ℕ) : ℝ) * ((g : ℝ) / 3) * utX n =
        ((4 / 3 : ℝ) * (utQ n : ℝ) * utX n) * (g : ℝ) := by push_cast; ring
    have h3 : (123 / 1000 : ℝ) * ((222 / 1000 : ℝ) * utY n) ^ 2 ≤
        (1 / (2 * ((255 / 1000 : ℝ) + 1 / (200 : ℝ))) - (180 / 100 : ℝ)) *
          ((222 / 1000 : ℝ) * utY n) ^ 2 :=
      mul_le_mul_of_nonneg_right heps (sq_nonneg _)
    rw [h2]
    exact mul_le_mul_of_nonneg_right (h1.trans h3) hg_posR.le
  have hshift_ub : ((g : ℝ) / 3) * utX n / (2 * (180 / 100 : ℝ) * ((222 / 1000 : ℝ) * utY n)) ≤
      ((3 / 5 : ℝ) * (utLn n : ℝ) + 4) * (g : ℝ) := by
    have hden_pos : 0 < 2 * (180 / 100 : ℝ) * ((222 / 1000 : ℝ) * utY n) := by linarith
    rw [div_le_iff₀ hden_pos, ← hYX]
    have hlog_le : Real.log (utX n) ≤ 3 * (2 * (180 / 100 : ℝ) * (222 / 1000 : ℝ)) * ((3 / 5 : ℝ) * (utLn n : ℝ) + 4) := by
      linarith
    have hp : 0 ≤ (g : ℝ) * utY n := mul_nonneg hg_posR.le hY_pos.le
    have hm := mul_le_mul_of_nonneg_right hlog_le hp
    linarith
  have hR0_eq : ((utSeedStages n * g : ℕ) : ℝ) = ((utLn n : ℝ) + 4) * (g : ℝ) := by
    dsimp [utSeedStages]; push_cast; ring
  have hR0_minus : (2 / 5 : ℝ) * (utLn n : ℝ) * (g : ℝ) ≤
      ((utSeedStages n * g : ℕ) : ℝ) - ((g : ℝ) / 3) * utX n / (2 * (180 / 100 : ℝ) * ((222 / 1000 : ℝ) * utY n)) := by
    linarith
  have hshift_pos : 0 < ((utSeedStages n * g : ℕ) : ℝ) -
      ((g : ℝ) / 3) * utX n / (2 * (180 / 100 : ℝ) * ((222 / 1000 : ℝ) * utY n)) := by
    nlinarith
  have hcap : (15 : ℝ) * (utLn n : ℝ) * (g : ℝ) ≤
      utX n / 200 - ((g : ℝ) / 3) * utX n / (2 * (180 / 100 : ℝ) * ((222 / 1000 : ℝ) * utY n)) := by
    have hLn_g_ub : (utLn n : ℝ) * (g : ℝ) ≤ 6 * (utLn n : ℝ) ^ 2 + 30 * (utLn n : ℝ) := by nlinarith
    have hn_le_X : (n : ℝ) ≤ utX n / 700000 := by
      dsimp [utX]; nlinarith
    linarith
  have hbud : Real.log (((15 : ℝ) * (utLn n : ℝ) * (g : ℝ)) /
      (((utSeedStages n * g : ℕ) : ℝ) - ((g : ℝ) / 3) * utX n / (2 * (180 / 100 : ℝ) * ((222 / 1000 : ℝ) * utY n)))) ≤
      ((180 / 100 : ℝ) * (g : ℝ) / (((g : ℝ) / 3) * utX n)) *
        ((utStepsAP1 n : ℝ) * ((509 / 2000 : ℝ) * utY n) -
          (utQ n : ℝ) * (utStepsAP1 n : ℝ) * ((utStepsAP1 n : ℝ) - 1)) /
          (1 + ((180 / 100 : ℝ) * (g : ℝ) / (((g : ℝ) / 3) * utX n)) * ((509 / 2000 : ℝ) * utY n)) := by
    have hquot_le : ((15 : ℝ) * (utLn n : ℝ) * (g : ℝ)) /
        (((utSeedStages n * g : ℕ) : ℝ) - ((g : ℝ) / 3) * utX n / (2 * (180 / 100 : ℝ) * ((222 / 1000 : ℝ) * utY n))) ≤ 38 := by
      rw [div_le_iff₀ hshift_pos]; nlinarith
    have hexp1_gt : (27182 / 10000 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have hlog38 : Real.log 38 < 37 / 10 := by
      have hp : (38 : ℝ) ^ 10 < (Real.exp 1) ^ 37 := by
        have h1 : (38 : ℝ) ^ 10 < (27182 / 10000 : ℝ) ^ 37 := by norm_num
        exact h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide))
      have h := Real.log_lt_log (by norm_num) hp
      rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h
      push_cast at h; linarith
    have hlhs_lt : Real.log (((15 : ℝ) * (utLn n : ℝ) * (g : ℝ)) /
        (((utSeedStages n * g : ℕ) : ℝ) - ((g : ℝ) / 3) * utX n / (2 * (180 / 100 : ℝ) * ((222 / 1000 : ℝ) * utY n)))) < 37 / 10 :=
      (Real.log_le_log (div_pos (by positivity) hshift_pos) hquot_le).trans_lt hlog38
    have halpha : (180 / 100 : ℝ) * (g : ℝ) / (((g : ℝ) / 3) * utX n) = (27 / 5 : ℝ) / utX n := by
      field_simp; ring
    have halpha_Ma : ((27 / 5 : ℝ) / utX n) * ((509 / 2000 : ℝ) * utY n) =
        (13743 / 10000 : ℝ) / Real.log (utX n) := by
      dsimp [utY]; field_simp; ring
    have hquad_lo : (utStepsAP1 n : ℝ) * ((477 / 2000 : ℝ) * utY n) ≤
        (utStepsAP1 n : ℝ) * ((509 / 2000 : ℝ) * utY n) -
          (utQ n : ℝ) * (utStepsAP1 n : ℝ) * ((utStepsAP1 n : ℝ) - 1) := by
      have hQ_steps : (utQ n : ℝ) * ((utStepsAP1 n : ℝ) - 1) ≤ (16 / 1000 : ℝ) * utY n := by
        have hs_pos : (1 : ℝ) ≤ (utStepsAP1 n : ℝ) := by
          dsimp [utStepsAP1]; push_cast; linarith
        nlinarith
      have hst_nn : (0 : ℝ) ≤ (utStepsAP1 n : ℝ) := Nat.cast_nonneg _
      nlinarith
    rw [halpha, halpha_Ma]
    have hnum_lo : ((27 / 5 * (477 / 2000) * 7 : ℝ) * (utLn n : ℝ)) / Real.log (utX n) ≤
        ((27 / 5 : ℝ) / utX n) *
          ((utStepsAP1 n : ℝ) * ((509 / 2000 : ℝ) * utY n) -
            (utQ n : ℝ) * (utStepsAP1 n : ℝ) * ((utStepsAP1 n : ℝ) - 1)) := by
      have h1 := mul_le_mul_of_nonneg_left hquad_lo (by positivity : (0 : ℝ) ≤ (27 / 5 : ℝ) / utX n)
      have h2 : ((27 / 5 : ℝ) / utX n) * ((utStepsAP1 n : ℝ) * ((477 / 2000 : ℝ) * utY n)) =
          ((27 / 5 * (477 / 2000) * 7 : ℝ) * (utLn n : ℝ)) / Real.log (utX n) := by
        dsimp [utStepsAP1, utY]; push_cast; field_simp
      rwa [← h2]
    have hden_pos : 0 < 1 + (13743 / 10000 : ℝ) / Real.log (utX n) := by positivity
    have h_le : (37 / 10 : ℝ) ≤ (((27 / 5 * (477 / 2000) * 7 : ℝ) * (utLn n : ℝ)) / Real.log (utX n)) /
        (1 + (13743 / 10000 : ℝ) / Real.log (utX n)) := by
      rw [le_div_iff₀ hden_pos]
      have hmul_log : (37 / 10 : ℝ) * (Real.log (utX n) + 13743 / 10000) ≤
          (27 / 5 * (477 / 2000) * 7 : ℝ) * (utLn n : ℝ) := by linarith
      have hd := div_le_div_of_nonneg_right hmul_log hlog_pos.le
      have heq_l : (37 / 10 : ℝ) * (1 + (13743 / 10000 : ℝ) / Real.log (utX n)) =
          ((37 / 10 : ℝ) * (Real.log (utX n) + 13743 / 10000)) / Real.log (utX n) := by field_simp
      rwa [← heq_l] at hd
    exact hlhs_lt.le.trans (h_le.trans (div_le_div_of_nonneg_right hnum_lo hden_pos.le))
  exact ⟨by norm_num, hstock, hfloor, hpair, hshift_pos, hcap, hbud⟩

/-- Scalar gates for the second `AP` subphase `AP_2` (`ap_narrow_linear_phase_from_scalar`) on `Pool 1 \ AP_1`
with `c = 255/1000, r = g / 3, L = 200, η = 158/100, Ma = 222/1000 * Y, Mf = 139/1000 * Y`,
`R1 ≥ 15 * utLn n * g`, `target = 12000 * utLn n * g`, `z = 2`. -/
theorem ut_ap2_scalar_gates
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n g R1 : ℕ} (hn : 35735 ≤ n) (hg_pos : 0 < g) (hg_dvd : 6 ∣ g) (hg_le : g ≤ utSeedCap n)
    (hR1 : (15 : ℝ) * (utLn n : ℝ) * (g : ℝ) ≤ (R1 : ℝ)) :
    let X := utX n
    let Y := utY n
    let r : ℝ := (g : ℝ) / 3
    let L : ℝ := 200
    let η : ℝ := 158 / 100
    let Ma : ℝ := (222 / 1000 : ℝ) * Y
    let Mf : ℝ := (139 / 1000 : ℝ) * Y
    let target : ℝ := (12000 : ℝ) * (utLn n : ℝ) * (g : ℝ)
    let steps := utStepsAP2 n
    let Q := utQ n
    Ma ≤ (509 / 2000 : ℝ) * Y - 2 * (Q : ℝ) * (utStepsAP1 n : ℝ) ∧
    0 ≤ 1 / (2 * ((255 / 1000 : ℝ) + 1 / L)) - η ∧
    2 * Q * steps < Nat.ceil Ma ∧
    Mf ≤ Ma - 2 * (Q : ℝ) * (steps : ℝ) ∧
    2 * ((2 * Q : ℕ) : ℝ) * r * X ≤ (1 / (2 * ((255 / 1000 : ℝ) + 1 / L)) - η) * Mf ^ 2 * (g : ℝ) ∧
    0 < (R1 : ℝ) - r * X / (2 * η * Mf) ∧
    target ≤ X / L - r * X / (2 * η * Mf) ∧
    Real.log (target / ((R1 : ℝ) - r * X / (2 * η * Mf))) ≤
      (η * (g : ℝ) / (r * X)) * ((steps : ℝ) * Ma - (Q : ℝ) * (steps : ℝ) * ((steps : ℝ) - 1)) /
        (1 + (η * (g : ℝ) / (r * X)) * Ma) := by
  obtain ⟨hlog24, _, hLn11, hlog_lo, hlog_hi, hY_gt, _, _, hLn_lin, hLn_sq⟩ :=
    ut_sharp_scale_bounds rs lower sharp upper hn
  have hlog_ub_n := ut_logX_lt_linear rs lower sharp upper hn
  obtain ⟨hX_sq, hX_283, _, _, _⟩ := poolMaximum_bounds_ge_35735 sharp upper hn
  have hX : (283 * 10 ^ 8 : ℝ) ≤ utX n := by dsimp [utX]; exact hX_283.le
  have hX_pos : 0 < utX n := by linarith
  have hlog_pos : 0 < Real.log (utX n) := by linarith
  have hYX : utY n * Real.log (utX n) = utX n := div_mul_cancel₀ _ hlog_pos.ne'
  have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hLnR : (11 : ℝ) ≤ (utLn n : ℝ) := by exact_mod_cast hLn11
  have hY_pos : 0 < utY n := by nlinarith
  have hg6 : 6 ≤ g := by obtain ⟨k, rfl⟩ := hg_dvd; omega
  have hgR : (6 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg6
  have hg_posR : (0 : ℝ) < (g : ℝ) := by linarith
  have hg_ub : (g : ℝ) ≤ 6 * ((utLn n : ℝ) + 5) := by
    have : (g : ℝ) ≤ (utSeedCap n : ℝ) := by exact_mod_cast hg_le
    dsimp [utSeedCap] at this; push_cast at this; linarith
  dsimp only
  have hMa_ap1 : (222 / 1000 : ℝ) * utY n ≤
      (509 / 2000 : ℝ) * utY n - 2 * (utQ n : ℝ) * (utStepsAP1 n : ℝ) :=
    (ut_ap1_scalar_gates rs lower sharp upper hn hg_pos hg_dvd hg_le).2.2.1
  have heps : (343 / 1000 : ℝ) ≤ 1 / (2 * ((255 / 1000 : ℝ) + 1 / (200 : ℝ))) - (158 / 100 : ℝ) := by norm_num
  have h2Qsteps : 2 * (utQ n : ℝ) * (utStepsAP2 n : ℝ) ≤ (83 / 1000 : ℝ) * utY n := by
    have h1 : 2 * (utQ n : ℝ) * (utStepsAP2 n : ℝ) = 38 * (utLn n : ℝ) * (6 * (n : ℝ) + 4) := by
      dsimp [utQ, utStepsAP2]; push_cast; ring
    have h6n4 : 6 * (n : ℝ) + 4 ≤ (6001 / 1000 : ℝ) * (n : ℝ) := by linarith
    have hp := mul_le_mul hLn_lin h6n4 (by positivity) (by positivity)
    rw [h1]; nlinarith
  have hfloor : (139 / 1000 : ℝ) * utY n ≤ (222 / 1000 : ℝ) * utY n - 2 * (utQ n : ℝ) * (utStepsAP2 n : ℝ) := by
    linarith
  have hstock : 2 * utQ n * utStepsAP2 n < Nat.ceil ((222 / 1000 : ℝ) * utY n) := by
    have hreal : ((2 * utQ n * utStepsAP2 n : ℕ) : ℝ) < (222 / 1000 : ℝ) * utY n := by
      push_cast; linarith
    exact_mod_cast hreal.trans_le (Nat.le_ceil _)
  have hpair : 2 * ((2 * utQ n : ℕ) : ℝ) * ((g : ℝ) / 3) * utX n ≤
      (1 / (2 * ((255 / 1000 : ℝ) + 1 / (200 : ℝ))) - (158 / 100 : ℝ)) *
        ((139 / 1000 : ℝ) * utY n) ^ 2 * (g : ℝ) := by
    have h1 : (4 / 3 : ℝ) * (utQ n : ℝ) * utX n ≤
        (343 / 1000 : ℝ) * ((139 / 1000 : ℝ) * utY n) ^ 2 := by
      have hQ_eq : (utQ n : ℝ) = 6 * (n : ℝ) + 4 := by dsimp [utQ]; push_cast; ring
      have hX_ub : utX n < (68 / 100000 : ℝ) * (n : ℝ) * utY n := by
        rw [← hYX]
        have hm := mul_lt_mul_of_pos_right hlog_ub_n hY_pos
        linarith
      have hQX : (utQ n : ℝ) * utX n ≤ ((6001 / 1000 : ℝ) * (n : ℝ)) * ((68 / 100000 : ℝ) * (n : ℝ) * utY n) := by
        rw [hQ_eq]; exact mul_le_mul (by linarith) hX_ub.le hX_pos.le (by positivity)
      have hY2 : (925 / 1000 : ℝ) * (n : ℝ) ^ 2 * utY n ≤ (utY n) ^ 2 := by
        have hm := mul_le_mul_of_nonneg_right hY_gt.le hY_pos.le
        linarith
      nlinarith
    have h2 : 2 * ((2 * utQ n : ℕ) : ℝ) * ((g : ℝ) / 3) * utX n =
        ((4 / 3 : ℝ) * (utQ n : ℝ) * utX n) * (g : ℝ) := by push_cast; ring
    have h3 : (343 / 1000 : ℝ) * ((139 / 1000 : ℝ) * utY n) ^ 2 ≤
        (1 / (2 * ((255 / 1000 : ℝ) + 1 / (200 : ℝ))) - (158 / 100 : ℝ)) *
          ((139 / 1000 : ℝ) * utY n) ^ 2 :=
      mul_le_mul_of_nonneg_right heps (sq_nonneg _)
    rw [h2]
    exact mul_le_mul_of_nonneg_right (h1.trans h3) hg_posR.le
  have hshift_ub : ((g : ℝ) / 3) * utX n / (2 * (158 / 100 : ℝ) * ((139 / 1000 : ℝ) * utY n)) ≤
      (17 / 10 : ℝ) * (utLn n : ℝ) * (g : ℝ) := by
    have hden_pos : 0 < 2 * (158 / 100 : ℝ) * ((139 / 1000 : ℝ) * utY n) := by linarith
    rw [div_le_iff₀ hden_pos, ← hYX]
    have hlog_le_Ln : Real.log (utX n) ≤ (49 / 22 : ℝ) * (utLn n : ℝ) := by linarith
    have hp : 0 ≤ (g : ℝ) * utY n := mul_nonneg hg_posR.le hY_pos.le
    have hm := mul_le_mul_of_nonneg_right hlog_le_Ln hp
    have hprod_nn : 0 ≤ (g : ℝ) * utY n * (utLn n : ℝ) := by positivity
    ring_nf at hm hprod_nn ⊢; linarith
  have hR1_minus : (133 / 10 : ℝ) * (utLn n : ℝ) * (g : ℝ) ≤
      (R1 : ℝ) - ((g : ℝ) / 3) * utX n / (2 * (158 / 100 : ℝ) * ((139 / 1000 : ℝ) * utY n)) := by
    linarith
  have hshift_pos : 0 < (R1 : ℝ) -
      ((g : ℝ) / 3) * utX n / (2 * (158 / 100 : ℝ) * ((139 / 1000 : ℝ) * utY n)) := by
    nlinarith
  have hcap : (12000 : ℝ) * (utLn n : ℝ) * (g : ℝ) ≤
      utX n / 200 - ((g : ℝ) / 3) * utX n / (2 * (158 / 100 : ℝ) * ((139 / 1000 : ℝ) * utY n)) := by
    have hLn_g_ub : (utLn n : ℝ) * (g : ℝ) ≤ 6 * (utLn n : ℝ) ^ 2 + 30 * (utLn n : ℝ) := by nlinarith
    have hn_le_X : (n : ℝ) ≤ utX n / 700000 := by
      dsimp [utX]; nlinarith
    linarith
  have hbud : Real.log (((12000 : ℝ) * (utLn n : ℝ) * (g : ℝ)) /
      ((R1 : ℝ) - ((g : ℝ) / 3) * utX n / (2 * (158 / 100 : ℝ) * ((139 / 1000 : ℝ) * utY n)))) ≤
      ((158 / 100 : ℝ) * (g : ℝ) / (((g : ℝ) / 3) * utX n)) *
        ((utStepsAP2 n : ℝ) * ((222 / 1000 : ℝ) * utY n) -
          (utQ n : ℝ) * (utStepsAP2 n : ℝ) * ((utStepsAP2 n : ℝ) - 1)) /
          (1 + ((158 / 100 : ℝ) * (g : ℝ) / (((g : ℝ) / 3) * utX n)) * ((222 / 1000 : ℝ) * utY n)) := by
    have hquot_le : ((12000 : ℝ) * (utLn n : ℝ) * (g : ℝ)) /
        ((R1 : ℝ) - ((g : ℝ) / 3) * utX n / (2 * (158 / 100 : ℝ) * ((139 / 1000 : ℝ) * utY n))) ≤ 903 := by
      rw [div_le_iff₀ hshift_pos]; nlinarith
    have hexp1_gt : (27182 / 10000 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have hlog903 : Real.log 903 < 69 / 10 := by
      have hp : (903 : ℝ) ^ 10 < (Real.exp 1) ^ 69 := by
        have h1 : (903 : ℝ) ^ 10 < (27182 / 10000 : ℝ) ^ 69 := by norm_num
        exact h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide))
      have h := Real.log_lt_log (by norm_num) hp
      rw [Real.log_pow, ← Real.exp_nat_mul, Real.log_exp] at h
      push_cast at h; linarith
    have hlhs_lt : Real.log (((12000 : ℝ) * (utLn n : ℝ) * (g : ℝ)) /
        ((R1 : ℝ) - ((g : ℝ) / 3) * utX n / (2 * (158 / 100 : ℝ) * ((139 / 1000 : ℝ) * utY n)))) < 69 / 10 :=
      (Real.log_le_log (div_pos (by positivity) hshift_pos) hquot_le).trans_lt hlog903
    have halpha : (158 / 100 : ℝ) * (g : ℝ) / (((g : ℝ) / 3) * utX n) = (237 / 50 : ℝ) / utX n := by
      field_simp; ring
    have halpha_Ma : ((237 / 50 : ℝ) / utX n) * ((222 / 1000 : ℝ) * utY n) =
        (52614 / 50000 : ℝ) / Real.log (utX n) := by
      dsimp [utY]; field_simp; ring
    have hquad_lo : (utStepsAP2 n : ℝ) * ((361 / 2000 : ℝ) * utY n) ≤
        (utStepsAP2 n : ℝ) * ((222 / 1000 : ℝ) * utY n) -
          (utQ n : ℝ) * (utStepsAP2 n : ℝ) * ((utStepsAP2 n : ℝ) - 1) := by
      have hQ_steps : (utQ n : ℝ) * ((utStepsAP2 n : ℝ) - 1) ≤ (83 / 2000 : ℝ) * utY n := by
        have hs_pos : (1 : ℝ) ≤ (utStepsAP2 n : ℝ) := by
          dsimp [utStepsAP2]; push_cast; linarith
        nlinarith
      have hst_nn : (0 : ℝ) ≤ (utStepsAP2 n : ℝ) := Nat.cast_nonneg _
      nlinarith
    rw [halpha, halpha_Ma]
    have hnum_lo : ((237 / 50 * (361 / 2000) * 19 : ℝ) * (utLn n : ℝ)) / Real.log (utX n) ≤
        ((237 / 50 : ℝ) / utX n) *
          ((utStepsAP2 n : ℝ) * ((222 / 1000 : ℝ) * utY n) -
            (utQ n : ℝ) * (utStepsAP2 n : ℝ) * ((utStepsAP2 n : ℝ) - 1)) := by
      have h1 := mul_le_mul_of_nonneg_left hquad_lo (by positivity : (0 : ℝ) ≤ (237 / 50 : ℝ) / utX n)
      have h2 : ((237 / 50 : ℝ) / utX n) * ((utStepsAP2 n : ℝ) * ((361 / 2000 : ℝ) * utY n)) =
          ((237 / 50 * (361 / 2000) * 19 : ℝ) * (utLn n : ℝ)) / Real.log (utX n) := by
        dsimp [utStepsAP2, utY]; push_cast; field_simp
      rwa [← h2]
    have hden_pos : 0 < 1 + (52614 / 50000 : ℝ) / Real.log (utX n) := by positivity
    have h_le : (69 / 10 : ℝ) ≤ (((237 / 50 * (361 / 2000) * 19 : ℝ) * (utLn n : ℝ)) / Real.log (utX n)) /
        (1 + (52614 / 50000 : ℝ) / Real.log (utX n)) := by
      rw [le_div_iff₀ hden_pos]
      have hmul_log : (69 / 10 : ℝ) * (Real.log (utX n) + 52614 / 50000) ≤
          (237 / 50 * (361 / 2000) * 19 : ℝ) * (utLn n : ℝ) := by linarith
      have hd := div_le_div_of_nonneg_right hmul_log hlog_pos.le
      have heq_l : (69 / 10 : ℝ) * (1 + (52614 / 50000 : ℝ) / Real.log (utX n)) =
          ((69 / 10 : ℝ) * (Real.log (utX n) + 52614 / 50000)) / Real.log (utX n) := by field_simp
      rwa [← heq_l] at hd
    exact hlhs_lt.le.trans (h_le.trans (div_le_div_of_nonneg_right hnum_lo hden_pos.le))
  exact ⟨hMa_ap1, by norm_num, hstock, hfloor, hpair, hshift_pos, hcap, hbud⟩

/-- Scalar gates for the `MV` phase (`mv_narrow_linear_phase_from_scalar`) on `Pool 2 \ Seed`
with `c = 255/1000, r = φ(g), L = 13, η = 118/100, ell = 7, Ma = 242/1000 * Y, Mf = 135/1000 * Y`,
`R0 ≥ 12000 * utLn n * g`, `target = (76 / 1000) * X`, `z = 2`. -/
theorem ut_mv_scalar_gates
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n g R0 : ℕ} (hn : 35735 ≤ n) (hg_pos : 0 < g) (hg_dvd : 6 ∣ g) (hg_le : g ≤ utSeedCap n)
    (hR0 : (12000 : ℝ) * (utLn n : ℝ) * (g : ℝ) ≤ (R0 : ℝ)) :
    let X := utX n
    let Y := utY n
    let r : ℝ := (Nat.totient g : ℝ)
    let L : ℝ := 13
    let η : ℝ := 118 / 100
    let ell : ℝ := 7
    let Ma : ℝ := (242 / 1000 : ℝ) * Y
    let Mf : ℝ := (135 / 1000 : ℝ) * Y
    let target : ℝ := (76 / 1000 : ℝ) * X
    let steps := utStepsMV n
    let Q := utQ n
    Ma ≤ (509 / 2000 : ℝ) * Y - 2 * (utSeedStages n : ℝ) * (Q : ℝ) ∧
    0 ≤ 1 / (2 * ((255 / 1000 : ℝ) + 1 / L)) - η ∧
    2 * Q * steps < Nat.ceil Ma ∧
    Mf ≤ Ma - 2 * (Q : ℝ) * (steps : ℝ) ∧
    2 * ((2 * Q : ℕ) : ℝ) * r * X ≤ (1 / (2 * ((255 / 1000 : ℝ) + 1 / L)) - η) * Mf ^ 2 * (g : ℝ) ∧
    0 < (R0 : ℝ) - r * X / (2 * η * Mf) ∧
    target ≤ X / L - r * X / (2 * η * Mf) ∧
    r * X * Real.exp ell / ((ell * (Nat.totient g : ℝ) / (2 * (g : ℝ))) * η * Mf) ≤
      (R0 : ℝ) - r * X / (2 * η * Mf) ∧
    Real.log (target / ((R0 : ℝ) - r * X / (2 * η * Mf))) ≤
      ((ell * (Nat.totient g : ℝ) / (2 * (g : ℝ))) * η * (g : ℝ) / (r * X)) *
        ((steps : ℝ) * Ma - (Q : ℝ) * (steps : ℝ) * ((steps : ℝ) - 1)) /
          (1 + ((ell * (Nat.totient g : ℝ) / (2 * (g : ℝ))) * η * (g : ℝ) / (r * X)) * Ma) := by
  obtain ⟨hlog24, _, hLn11, hlog_lo, hlog_hi, hY_gt, _, _, hLn_lin, hLn_sq⟩ :=
    ut_sharp_scale_bounds rs lower sharp upper hn
  have hlog_ub_n := ut_logX_lt_linear rs lower sharp upper hn
  obtain ⟨hsteps_lin, _⟩ := ut_quadratic_step_bounds rs lower sharp upper hn
  obtain ⟨hphi_ge2, hphi_3le⟩ := ut_totient_six_dvd_bounds hg_pos hg_dvd
  obtain ⟨hX_sq, hX_283, _, _, _⟩ := poolMaximum_bounds_ge_35735 sharp upper hn
  have hX : (283 * 10 ^ 8 : ℝ) ≤ utX n := by dsimp [utX]; exact hX_283.le
  have hX_pos : 0 < utX n := by linarith
  have hlog_pos : 0 < Real.log (utX n) := by linarith
  have hYX : utY n * Real.log (utX n) = utX n := div_mul_cancel₀ _ hlog_pos.ne'
  have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hLnR : (11 : ℝ) ≤ (utLn n : ℝ) := by exact_mod_cast hLn11
  have hY_pos : 0 < utY n := by nlinarith
  have hg6 : 6 ≤ g := by obtain ⟨k, rfl⟩ := hg_dvd; omega
  have hgR : (6 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg6
  have hg_posR : (0 : ℝ) < (g : ℝ) := by linarith
  have hphi_pos : (0 : ℝ) < (Nat.totient g : ℝ) := by
    have : (2 : ℝ) ≤ (Nat.totient g : ℝ) := by exact_mod_cast hphi_ge2
    linarith
  have hphi_le_g3 : (Nat.totient g : ℝ) ≤ (g : ℝ) / 3 := by
    have : 3 * (Nat.totient g : ℝ) ≤ (g : ℝ) := by exact_mod_cast hphi_3le
    linarith
  have hg_ub : (g : ℝ) ≤ 6 * ((utLn n : ℝ) + 5) := by
    have : (g : ℝ) ≤ (utSeedCap n : ℝ) := by exact_mod_cast hg_le
    dsimp [utSeedCap] at this; push_cast at this; linarith
  dsimp only
  have hMa_seed : (242 / 1000 : ℝ) * utY n ≤
      (509 / 2000 : ℝ) * utY n - 2 * (utSeedStages n : ℝ) * (utQ n : ℝ) := by
    have h1 : 2 * (utSeedStages n : ℝ) * (utQ n : ℝ) = 2 * ((utLn n : ℝ) + 4) * (6 * (n : ℝ) + 4) := by
      dsimp [utSeedStages, utQ]; push_cast; ring
    have hLn4 : (utLn n : ℝ) + 4 ≤ (5 / 10000 : ℝ) * (n : ℝ) := by linarith
    have h6n4 : 6 * (n : ℝ) + 4 ≤ (6001 / 1000 : ℝ) * (n : ℝ) := by linarith
    have hp := mul_le_mul hLn4 h6n4 (by positivity) (by positivity)
    rw [h1]; nlinarith
  have heps : (326 / 1000 : ℝ) ≤ 1 / (2 * ((255 / 1000 : ℝ) + 1 / (13 : ℝ))) - (118 / 100 : ℝ) := by norm_num
  have h2Qsteps : 2 * (utQ n : ℝ) * (utStepsMV n : ℝ) ≤ (107 / 1000 : ℝ) * utY n := by
    have hQ_eq : (utQ n : ℝ) = 6 * (n : ℝ) + 4 := by dsimp [utQ]; push_cast; ring
    have h6n4 : 6 * (n : ℝ) + 4 ≤ (6001 / 1000 : ℝ) * (n : ℝ) := by linarith
    have hp := mul_le_mul h6n4 hsteps_lin (Nat.cast_nonneg _) (by positivity)
    rw [hQ_eq]; nlinarith
  have hfloor : (135 / 1000 : ℝ) * utY n ≤ (242 / 1000 : ℝ) * utY n - 2 * (utQ n : ℝ) * (utStepsMV n : ℝ) := by
    linarith
  have hstock : 2 * utQ n * utStepsMV n < Nat.ceil ((242 / 1000 : ℝ) * utY n) := by
    have hreal : ((2 * utQ n * utStepsMV n : ℕ) : ℝ) < (242 / 1000 : ℝ) * utY n := by
      push_cast; linarith
    exact_mod_cast hreal.trans_le (Nat.le_ceil _)
  have hpair : 2 * ((2 * utQ n : ℕ) : ℝ) * (Nat.totient g : ℝ) * utX n ≤
      (1 / (2 * ((255 / 1000 : ℝ) + 1 / (13 : ℝ))) - (118 / 100 : ℝ)) *
        ((135 / 1000 : ℝ) * utY n) ^ 2 * (g : ℝ) := by
    have h1 : (4 / 3 : ℝ) * (utQ n : ℝ) * utX n ≤
        (326 / 1000 : ℝ) * ((135 / 1000 : ℝ) * utY n) ^ 2 := by
      have hQ_eq : (utQ n : ℝ) = 6 * (n : ℝ) + 4 := by dsimp [utQ]; push_cast; ring
      have hX_ub : utX n < (68 / 100000 : ℝ) * (n : ℝ) * utY n := by
        rw [← hYX]
        have hm := mul_lt_mul_of_pos_right hlog_ub_n hY_pos
        linarith
      have hQX : (utQ n : ℝ) * utX n ≤ ((6001 / 1000 : ℝ) * (n : ℝ)) * ((68 / 100000 : ℝ) * (n : ℝ) * utY n) := by
        rw [hQ_eq]; exact mul_le_mul (by linarith) hX_ub.le hX_pos.le (by positivity)
      have hY2 : (925 / 1000 : ℝ) * (n : ℝ) ^ 2 * utY n ≤ (utY n) ^ 2 := by
        have hm := mul_le_mul_of_nonneg_right hY_gt.le hY_pos.le
        linarith
      nlinarith
    have h2 : 2 * ((2 * utQ n : ℕ) : ℝ) * (Nat.totient g : ℝ) * utX n ≤
        ((4 / 3 : ℝ) * (utQ n : ℝ) * utX n) * (g : ℝ) := by
      push_cast
      have hp := mul_le_mul_of_nonneg_left hphi_le_g3 (by positivity : (0 : ℝ) ≤ 2 * (2 * (utQ n : ℝ)) * utX n)
      nlinarith
    have h3 : (326 / 1000 : ℝ) * ((135 / 1000 : ℝ) * utY n) ^ 2 * (g : ℝ) ≤
        (1 / (2 * ((255 / 1000 : ℝ) + 1 / (13 : ℝ))) - (118 / 100 : ℝ)) *
          ((135 / 1000 : ℝ) * utY n) ^ 2 * (g : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right heps (sq_nonneg _)) hg_posR.le
    exact h2.trans ((mul_le_mul_of_nonneg_right h1 hg_posR.le).trans h3)
  have hshift_ub : (Nat.totient g : ℝ) * utX n / (2 * (118 / 100 : ℝ) * ((135 / 1000 : ℝ) * utY n)) ≤
      3 * (utLn n : ℝ) * (g : ℝ) := by
    have hden_pos : 0 < 2 * (118 / 100 : ℝ) * ((135 / 1000 : ℝ) * utY n) := by linarith
    rw [div_le_iff₀ hden_pos, ← hYX]
    have hlog_le_Ln : Real.log (utX n) ≤ (49 / 22 : ℝ) * (utLn n : ℝ) := by linarith
    have hp1 : (Nat.totient g : ℝ) * (utY n * Real.log (utX n)) ≤
        ((g : ℝ) / 3) * (utY n * ((49 / 22 : ℝ) * (utLn n : ℝ))) :=
      mul_le_mul hphi_le_g3 (mul_le_mul_of_nonneg_left hlog_le_Ln hY_pos.le)
        (by positivity) (by positivity)
    have hprod_nn : 0 ≤ utY n * (g : ℝ) * (utLn n : ℝ) := by positivity
    ring_nf at hp1 hprod_nn ⊢; linarith
  have hR0_minus : (11997 : ℝ) * (utLn n : ℝ) * (g : ℝ) ≤
      (R0 : ℝ) - (Nat.totient g : ℝ) * utX n / (2 * (118 / 100 : ℝ) * ((135 / 1000 : ℝ) * utY n)) := by
    linarith
  have hshift_pos : 0 < (R0 : ℝ) -
      (Nat.totient g : ℝ) * utX n / (2 * (118 / 100 : ℝ) * ((135 / 1000 : ℝ) * utY n)) := by nlinarith
  have hcap : (76 / 1000 : ℝ) * utX n ≤
      utX n / 13 - (Nat.totient g : ℝ) * utX n / (2 * (118 / 100 : ℝ) * ((135 / 1000 : ℝ) * utY n)) := by
    have hLn_g_ub : (utLn n : ℝ) * (g : ℝ) ≤ 6 * (utLn n : ℝ) ^ 2 + 30 * (utLn n : ℝ) := by nlinarith
    have hn_le_X : (n : ℝ) ≤ utX n / 700000 := by
      dsimp [utX]; nlinarith
    linarith
  have hexp1_lt : Real.exp 1 < 27183 / 10000 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hpaid : (Nat.totient g : ℝ) * utX n * Real.exp 7 /
      (((7 : ℝ) * (Nat.totient g : ℝ) / (2 * (g : ℝ))) * (118 / 100 : ℝ) * ((135 / 1000 : ℝ) * utY n)) ≤
      (R0 : ℝ) - (Nat.totient g : ℝ) * utX n / (2 * (118 / 100 : ℝ) * ((135 / 1000 : ℝ) * utY n)) := by
    have hexp7 : Real.exp 7 < 1097 := by
      have h1 : Real.exp 7 = (Real.exp 1) ^ 7 := by
        have : (7 : ℝ) = ((7 : ℕ) : ℝ) * 1 := by norm_num
        rw [this, Real.exp_nat_mul]
      rw [h1]
      exact (pow_lt_pow_left₀ hexp1_lt (Real.exp_pos 1).le (by decide)).trans (by norm_num)
    have hsimp : (Nat.totient g : ℝ) * utX n * Real.exp 7 /
        (((7 : ℝ) * (Nat.totient g : ℝ) / (2 * (g : ℝ))) * (118 / 100 : ℝ) * ((135 / 1000 : ℝ) * utY n)) =
        (2 * Real.exp 7 / (7 * (118 / 100) * (135 / 1000))) * Real.log (utX n) * (g : ℝ) := by
      dsimp [utY]; field_simp
    rw [hsimp]
    have hlog_le_Ln : Real.log (utX n) ≤ (49 / 22 : ℝ) * (utLn n : ℝ) := by linarith
    have hp1 : (2 * Real.exp 7 / (7 * (118 / 100) * (135 / 1000))) * Real.log (utX n) ≤
        (2 * 1097 / (7 * (118 / 100) * (135 / 1000))) * ((49 / 22 : ℝ) * (utLn n : ℝ)) :=
      mul_le_mul (div_le_div_of_nonneg_right (by linarith) (by norm_num))
        hlog_le_Ln hlog_pos.le (by norm_num)
    have hp1' : (2 * Real.exp 7 / (7 * (118 / 100) * (135 / 1000))) * Real.log (utX n) ≤
        11997 * (utLn n : ℝ) :=
      hp1.trans (by linarith)
    exact (mul_le_mul_of_nonneg_right hp1' hg_posR.le).trans hR0_minus
  have hbud : Real.log (((76 / 1000 : ℝ) * utX n) /
      ((R0 : ℝ) - (Nat.totient g : ℝ) * utX n / (2 * (118 / 100 : ℝ) * ((135 / 1000 : ℝ) * utY n)))) ≤
      (((7 : ℝ) * (Nat.totient g : ℝ) / (2 * (g : ℝ))) * (118 / 100 : ℝ) * (g : ℝ) / ((Nat.totient g : ℝ) * utX n)) *
        ((utStepsMV n : ℝ) * ((242 / 1000 : ℝ) * utY n) -
          (utQ n : ℝ) * (utStepsMV n : ℝ) * ((utStepsMV n : ℝ) - 1)) /
          (1 + (((7 : ℝ) * (Nat.totient g : ℝ) / (2 * (g : ℝ))) * (118 / 100 : ℝ) * (g : ℝ) / ((Nat.totient g : ℝ) * utX n)) *
            ((242 / 1000 : ℝ) * utY n)) := by
    have hR0_num : (791802 : ℝ) ≤
        (R0 : ℝ) - (Nat.totient g : ℝ) * utX n / (2 * (118 / 100 : ℝ) * ((135 / 1000 : ℝ) * utY n)) := by
      have : (66 : ℝ) ≤ (utLn n : ℝ) * (g : ℝ) := by nlinarith
      linarith
    have hquot_le : ((76 / 1000 : ℝ) * utX n) /
        ((R0 : ℝ) - (Nat.totient g : ℝ) * utX n / (2 * (118 / 100 : ℝ) * ((135 / 1000 : ℝ) * utY n))) ≤
        utX n / 9500000 := by
      rw [div_le_iff₀ hshift_pos]
      have hp := mul_le_mul_of_nonneg_left hR0_num hX_pos.le
      linarith
    have hlog95 : (16 : ℝ) < Real.log 9500000 := by
      have hp : (Real.exp 1) ^ 16 < (9500000 : ℝ) :=
        (pow_lt_pow_left₀ hexp1_lt (Real.exp_pos 1).le (by decide)).trans (by norm_num)
      have h := Real.log_lt_log (pow_pos (Real.exp_pos 1) 16) hp
      rw [← Real.exp_nat_mul, Real.log_exp] at h
      push_cast at h; linarith
    have hlhs_ub : Real.log (((76 / 1000 : ℝ) * utX n) /
        ((R0 : ℝ) - (Nat.totient g : ℝ) * utX n / (2 * (118 / 100 : ℝ) * ((135 / 1000 : ℝ) * utY n)))) <
        (utLn n : ℝ) - 5 / 2 := by
      have h1 := Real.log_le_log (div_pos (by positivity) hshift_pos) hquot_le
      rw [Real.log_div hX_pos.ne' (by norm_num)] at h1
      linarith
    have halpha : ((7 : ℝ) * (Nat.totient g : ℝ) / (2 * (g : ℝ))) * (118 / 100 : ℝ) * (g : ℝ) /
        ((Nat.totient g : ℝ) * utX n) = (413 / 100 : ℝ) / utX n := by
      field_simp; ring
    have halpha_Ma : ((413 / 100 : ℝ) / utX n) * ((242 / 1000 : ℝ) * utY n) =
        (413 * 242 / 100000 : ℝ) / Real.log (utX n) := by
      dsimp [utY]; field_simp; ring
    have hquad_lo : (utStepsMV n : ℝ) * ((1875 / 10000 : ℝ) * utY n) ≤
        (utStepsMV n : ℝ) * ((242 / 1000 : ℝ) * utY n) -
          (utQ n : ℝ) * (utStepsMV n : ℝ) * ((utStepsMV n : ℝ) - 1) := by
      have hs_pos : (1 : ℝ) ≤ (utStepsMV n : ℝ) := by
        have : 26 * 11 ≤ utStepsMV n := by dsimp [utStepsMV]; omega
        exact_mod_cast (show 1 ≤ utStepsMV n by omega)
      have hQ_steps : (utQ n : ℝ) * ((utStepsMV n : ℝ) - 1) ≤ (107 / 2000 : ℝ) * utY n := by nlinarith
      have hst_nn : (0 : ℝ) ≤ (utStepsMV n : ℝ) := Nat.cast_nonneg _
      nlinarith
    rw [halpha, halpha_Ma]
    have hnum_lo : ((1239 / 1600 : ℝ) * (utStepsMV n : ℝ)) / Real.log (utX n) ≤
        ((413 / 100 : ℝ) / utX n) *
          ((utStepsMV n : ℝ) * ((242 / 1000 : ℝ) * utY n) -
            (utQ n : ℝ) * (utStepsMV n : ℝ) * ((utStepsMV n : ℝ) - 1)) := by
      have h1 := mul_le_mul_of_nonneg_left hquad_lo (by positivity : (0 : ℝ) ≤ (413 / 100 : ℝ) / utX n)
      have h2 : ((413 / 100 : ℝ) / utX n) * ((utStepsMV n : ℝ) * ((1875 / 10000 : ℝ) * utY n)) =
          ((1239 / 1600 : ℝ) * (utStepsMV n : ℝ)) / Real.log (utX n) := by
        dsimp [utY]; field_simp; ring
      rwa [← h2]
    have hden_pos : 0 < 1 + (413 * 242 / 100000 : ℝ) / Real.log (utX n) := by positivity
    have hrhs_ge : (utLn n : ℝ) - 5 / 2 ≤
        (((1239 / 1600 : ℝ) * (utStepsMV n : ℝ)) / Real.log (utX n)) /
          (1 + (413 * 242 / 100000 : ℝ) / Real.log (utX n)) := by
      rw [le_div_iff₀ hden_pos]
      have hsteps_poly : (utStepsMV n : ℝ) =
          2 * ((utLn n : ℝ) - 11) ^ 2 + 48 * ((utLn n : ℝ) - 11) + 286 := by
        have hnat : utStepsMV n = 26 * utLn n + 2 * (utLn n - 11) * utLn n := rfl
        have hsub_cast : ((utLn n - 11 : ℕ) : ℝ) = (utLn n : ℝ) - 11 := Nat.cast_sub hLn11
        have hc := congrArg (fun m : ℕ => (m : ℝ)) hnat
        push_cast at hc; rw [hsub_cast] at hc; linarith
      have hu_nn : 0 ≤ (utLn n : ℝ) - 11 := by linarith
      have hmul_log : ((utLn n : ℝ) - 5 / 2) * (Real.log (utX n) + 413 * 242 / 100000) ≤
          (1239 / 1600 : ℝ) * (utStepsMV n : ℝ) := by
        have hlog_step : Real.log (utX n) + 413 * 242 / 100000 ≤ ((utLn n : ℝ) - 11) + 51 / 2 := by linarith
        have h1 : ((utLn n : ℝ) - 5 / 2) * (Real.log (utX n) + 413 * 242 / 100000) ≤
            (((utLn n : ℝ) - 11) + 17 / 2) * (((utLn n : ℝ) - 11) + 51 / 2) :=
          mul_le_mul (by linarith) hlog_step (by positivity) (by linarith)
        rw [hsteps_poly]
        nlinarith [sq_nonneg ((utLn n : ℝ) - 11)]
      have hd := div_le_div_of_nonneg_right hmul_log hlog_pos.le
      have heq_l : ((utLn n : ℝ) - 5 / 2) * (1 + (413 * 242 / 100000 : ℝ) / Real.log (utX n)) =
          (((utLn n : ℝ) - 5 / 2) * (Real.log (utX n) + 413 * 242 / 100000)) / Real.log (utX n) := by
        field_simp
      rwa [← heq_l] at hd
    exact hlhs_ub.le.trans (hrhs_ge.trans (div_le_div_of_nonneg_right hnum_lo hden_pos.le))
  exact ⟨hMa_seed, by norm_num, hstock, hfloor, hpair, hshift_pos, hcap, hpaid, hbud⟩

/-- Scalar gates for the `StepBoost` phase on `Pool 2` (`ap_narrow_interval_stage`
at `R = (76 / 1000) * utX n`, `L = 1000 / 76`, `η = 93 / 100`, `Q_cand = 2 * utQ n`), ensuring at least
`(104 / 1000) * utY n` primes remain throughout and `R_g_boosted - R_mod ≥ (10 / 1000) * utX n`. -/
theorem ut_boost_scalar_gates
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n g h0 : ℕ} (hn : 35735 ≤ n) (hg_pos : 0 < g) (hg6 : 6 ∣ g) (hg_le : g ≤ utSeedCap n)
    (hh0 : h0 ≤ utH0Max n) :
    (104 / 1000 : ℝ) * utY n ≤
      (135 / 1000 : ℝ) * utY n - 4 * (utQ n : ℝ) * (utStepsBoost n : ℝ) ∧
    (0 : ℝ) ≤ 1 / (2 * ((255 / 1000 : ℝ) + 1 / (1000 / 76 : ℝ))) - (93 / 100 : ℝ) ∧
    2 * ((2 * utQ n : ℕ) : ℝ) * (Nat.totient g : ℝ) * utX n ≤
      (1 / (2 * ((255 / 1000 : ℝ) + 1 / (1000 / 76 : ℝ))) - (93 / 100 : ℝ)) *
        ((104 / 1000 : ℝ) * utY n) ^ 2 * (g : ℝ) ∧
    (22 / 1000 : ℝ) * utY n ≤
      (g : ℝ) * ((93 / 100 : ℝ) * ((104 / 1000 : ℝ) * utY n) * ((76 / 1000 : ℝ) * utX n) /
        ((Nat.totient g : ℝ) * utX n) - 1 / 2) ∧
    ((h0 - 1 : ℕ) : ℝ) * ((12 / 10000 : ℝ) * utX n) + (10 / 1000 : ℝ) * utX n ≤
      (76 / 1000 : ℝ) * utX n + (utStepsBoost n : ℝ) * ((22 / 1000 : ℝ) * utY n) := by
  obtain ⟨hlog24, _, hLn11, _, hlog_hi, hY_gt, _, _, hLn_lin, _⟩ :=
    ut_sharp_scale_bounds rs lower sharp upper hn
  have hlog_ub_n := ut_logX_lt_linear rs lower sharp upper hn
  obtain ⟨_, _, hboost_n, _⟩ := ut_ln14_step_bounds rs lower sharp upper hn
  obtain ⟨hphi_ge2, hphi_3le⟩ := ut_totient_six_dvd_bounds hg_pos hg6
  have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hX_pos : 0 < utX n := by dsimp [utX]; exact_mod_cast (poolMaximum_prime n).pos
  have hlog_pos : 0 < Real.log (utX n) := by linarith
  have hYX : utY n * Real.log (utX n) = utX n := div_mul_cancel₀ _ hlog_pos.ne'
  have hY_pos : 0 < utY n := by nlinarith
  have hg_posR : (0 : ℝ) < (g : ℝ) := Nat.cast_pos.mpr hg_pos
  have hphi_pos : (0 : ℝ) < (Nat.totient g : ℝ) := by
    have : (2 : ℝ) ≤ (Nat.totient g : ℝ) := by exact_mod_cast hphi_ge2
    linarith
  have hphi_le_g3 : (Nat.totient g : ℝ) ≤ (g : ℝ) / 3 := by
    have : 3 * (Nat.totient g : ℝ) ≤ (g : ℝ) := by exact_mod_cast hphi_3le
    linarith
  have hg_ub : (g : ℝ) ≤ 6 * ((utLn n : ℝ) + 5) := by
    have : (g : ℝ) ≤ (utSeedCap n : ℝ) := by exact_mod_cast hg_le
    dsimp [utSeedCap] at this; push_cast at this; linarith
  have hstock : (104 / 1000 : ℝ) * utY n ≤
      (135 / 1000 : ℝ) * utY n - 4 * (utQ n : ℝ) * (utStepsBoost n : ℝ) := by
    have hQ_eq : (utQ n : ℝ) = 6 * (n : ℝ) + 4 := by dsimp [utQ]; push_cast; ring
    have h6n4 : 6 * (n : ℝ) + 4 ≤ (6001 / 1000 : ℝ) * (n : ℝ) := by linarith
    have hp := mul_le_mul h6n4 hboost_n (Nat.cast_nonneg _) (by positivity)
    rw [hQ_eq]; nlinarith
  have heps : (58 / 100 : ℝ) ≤ 1 / (2 * ((255 / 1000 : ℝ) + 1 / (1000 / 76 : ℝ))) - (93 / 100 : ℝ) := by norm_num
  have hBT5 : 2 * ((2 * utQ n : ℕ) : ℝ) * (Nat.totient g : ℝ) * utX n ≤
      (1 / (2 * ((255 / 1000 : ℝ) + 1 / (1000 / 76 : ℝ))) - (93 / 100 : ℝ)) *
        ((104 / 1000 : ℝ) * utY n) ^ 2 * (g : ℝ) := by
    have h1 : (4 / 3 : ℝ) * (utQ n : ℝ) * utX n ≤
        (58 / 100 : ℝ) * ((104 / 1000 : ℝ) * utY n) ^ 2 := by
      have hQ_eq : (utQ n : ℝ) = 6 * (n : ℝ) + 4 := by dsimp [utQ]; push_cast; ring
      have hX_ub : utX n < (68 / 100000 : ℝ) * (n : ℝ) * utY n := by
        rw [← hYX]
        have hm := mul_lt_mul_of_pos_right hlog_ub_n hY_pos
        linarith
      have hQX : (utQ n : ℝ) * utX n ≤ ((6001 / 1000 : ℝ) * (n : ℝ)) * ((68 / 100000 : ℝ) * (n : ℝ) * utY n) := by
        rw [hQ_eq]; exact mul_le_mul (by linarith) hX_ub.le hX_pos.le (by positivity)
      have hY2 : (925 / 1000 : ℝ) * (n : ℝ) ^ 2 * utY n ≤ (utY n) ^ 2 := by
        have hm := mul_le_mul_of_nonneg_right hY_gt.le hY_pos.le
        linarith
      nlinarith
    have h2 : 2 * ((2 * utQ n : ℕ) : ℝ) * (Nat.totient g : ℝ) * utX n ≤
        ((4 / 3 : ℝ) * (utQ n : ℝ) * utX n) * (g : ℝ) := by
      push_cast
      have hp := mul_le_mul_of_nonneg_left hphi_le_g3 (by positivity : (0 : ℝ) ≤ 2 * (2 * (utQ n : ℝ)) * utX n)
      nlinarith
    have h3 : (58 / 100 : ℝ) * ((104 / 1000 : ℝ) * utY n) ^ 2 * (g : ℝ) ≤
        (1 / (2 * ((255 / 1000 : ℝ) + 1 / (1000 / 76 : ℝ))) - (93 / 100 : ℝ)) *
          ((104 / 1000 : ℝ) * utY n) ^ 2 * (g : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right heps (sq_nonneg _)) hg_posR.le
    exact h2.trans ((mul_le_mul_of_nonneg_right h1 hg_posR.le).trans h3)
  have hwidth : (22 / 1000 : ℝ) * utY n ≤
      (g : ℝ) * ((93 / 100 : ℝ) * ((104 / 1000 : ℝ) * utY n) * ((76 / 1000 : ℝ) * utX n) /
        ((Nat.totient g : ℝ) * utX n) - 1 / 2) := by
    have hsimp : (g : ℝ) * ((93 / 100 : ℝ) * ((104 / 1000 : ℝ) * utY n) * ((76 / 1000 : ℝ) * utX n) /
        ((Nat.totient g : ℝ) * utX n) - 1 / 2) =
        ((93 * 104 * 76 / 100000000 : ℝ) * utY n * (g : ℝ)) / (Nat.totient g : ℝ) - (g : ℝ) / 2 := by
      field_simp; ring
    rw [hsimp]
    have hdiv_ge : (3 * 93 * 104 * 76 / 100000000 : ℝ) * utY n ≤
        ((93 * 104 * 76 / 100000000 : ℝ) * utY n * (g : ℝ)) / (Nat.totient g : ℝ) := by
      rw [le_div_iff₀ hphi_pos]
      have hp := mul_le_mul_of_nonneg_left hphi_le_g3
        (show 0 ≤ (3 * 93 * 104 * 76 / 100000000 : ℝ) * utY n by linarith)
      linarith
    have hg_Y : (g : ℝ) ≤ (1 / 10000 : ℝ) * utY n := by nlinarith
    linarith
  have hgain : ((h0 - 1 : ℕ) : ℝ) * ((12 / 10000 : ℝ) * utX n) + (10 / 1000 : ℝ) * utX n ≤
      (76 / 1000 : ℝ) * utX n + (utStepsBoost n : ℝ) * ((22 / 1000 : ℝ) * utY n) := by
    by_cases hLn13 : utLn n ≤ 13
    · have hh0_53 : ((h0 - 1 : ℕ) : ℝ) ≤ 53 := by
        have : h0 - 1 ≤ 53 := by dsimp [utH0Max] at hh0; omega
        exact_mod_cast this
      have hnn : 0 ≤ (utStepsBoost n : ℝ) * ((22 / 1000 : ℝ) * utY n) :=
        mul_nonneg (Nat.cast_nonneg _) (by linarith)
      nlinarith
    · have h14 : 14 ≤ utLn n := by omega
      have h14R : (14 : ℝ) ≤ (utLn n : ℝ) := by exact_mod_cast h14
      let H := utH0Max n
      have hH_eq : (H : ℝ) = 3 * ((utLn n : ℝ) + 5) := by dsimp [H, utH0Max]; push_cast; ring
      have hH_pos : 0 < (H : ℝ) := by linarith
      have hlog_le_H2 : Real.log (utX n) ≤ (H : ℝ) / 2 := by linarith
      have hY_ge_HX : 2 * utX n / (H : ℝ) ≤ utY n := by
        dsimp [utY]
        rw [div_le_div_iff₀ hH_pos hlog_pos]
        nlinarith
      have hboost_ge : (H : ℝ) ^ 2 / 30 ≤ (utStepsBoost n : ℝ) := by
        have hnat : H * H ≤ utStepsBoost n * 30 := by
          dsimp [utStepsBoost, H]; rw [if_neg hLn13]; omega
        have hR : ((H : ℝ)) ^ 2 ≤ (utStepsBoost n : ℝ) * 30 := by
          have := (show ((H * H : ℕ) : ℝ) ≤ ((utStepsBoost n * 30 : ℕ) : ℝ) by exact_mod_cast hnat)
          push_cast at this; nlinarith
        linarith
      have hprod1 : ((H : ℝ) ^ 2 / 30) * ((22 / 1000 : ℝ) * (2 * utX n / (H : ℝ))) ≤
          (utStepsBoost n : ℝ) * ((22 / 1000 : ℝ) * utY n) :=
        mul_le_mul hboost_ge (mul_le_mul_of_nonneg_left hY_ge_HX (by norm_num))
          (by positivity) (Nat.cast_nonneg _)
      have hprod_eq : ((H : ℝ) ^ 2 / 30) * ((22 / 1000 : ℝ) * (2 * utX n / (H : ℝ))) =
          (44 / 30000 : ℝ) * (H : ℝ) * utX n := by
        field_simp; ring
      have hh0_le : ((h0 - 1 : ℕ) : ℝ) ≤ (H : ℝ) := by
        exact_mod_cast (show h0 - 1 ≤ H by omega)
      rw [hprod_eq] at hprod1
      nlinarith
  exact ⟨hstock, by norm_num, hBT5, hwidth, hgain⟩

/-- Universal power gate `b ^ 2 ≤ ((w * utX n) / (2 * p)) ^ 5` for `apInterval_filter_mod_two_prime_sharp`
whenever `0 < b ≤ utX n`, `6 / 10000 ≤ w`, `2 ≤ p ≤ utH0Max n`, and `35735 ≤ n`. -/
private theorem ut_mod_sharp_exp_gate
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n p : ℕ} {b c : ℝ} (hn : 35735 ≤ n) (hp_ge2 : 2 ≤ p) (hpH : p ≤ utH0Max n)
    (hb_pos : 0 < b) (hc_le : c ≤ utX n) (hb_le_c : b ≤ c)
    (hw : (6 / 10000 : ℝ) * utX n ≤ c - b) :
    Real.exp ((2 / 5 : ℝ) * Real.log b) ≤ (c - b) / (2 * p) := by
  obtain ⟨_, hLn_lo_all⟩ := (ut_sharp_scale_bounds rs lower sharp upper hn).2.2
  obtain ⟨_, hX_283, _, _, _⟩ := poolMaximum_bounds_ge_35735 sharp upper hn
  have hX : (283 * 10 ^ 8 : ℝ) ≤ utX n := by dsimp [utX]; linarith
  have hX_pos : 0 < utX n := by linarith
  let H := utH0Max n
  have hH_le_log : (H : ℝ) ≤ 3 * Real.log (utX n) := by
    have hlog_lo := hLn_lo_all.1
    have : (H : ℝ) = 3 * ((utLn n : ℝ) + 5) := by dsimp [H, utH0Max]; push_cast; ring
    linarith
  let u : ℝ := utX n / (283 * 10 ^ 8)
  have hu1 : 1 ≤ u := by dsimp [u]; linarith
  have hu_pos : 0 < u := by linarith
  have hlog_u_nn : 0 ≤ Real.log u := Real.log_nonneg hu1
  have hexp1_gt : (27182 / 10000 : ℝ) < Real.exp 1 :=
    lt_trans (by norm_num) Real.exp_one_gt_d9
  have hlog_base : Real.log (283 * 10 ^ 8 : ℝ) < 25 := by
    have hp : (283 * 10 ^ 8 : ℝ) < (Real.exp 1) ^ 25 := by
      have h1 : (283 * 10 ^ 8 : ℝ) < (27182 / 10000 : ℝ) ^ 25 := by norm_num
      exact h1.trans (pow_lt_pow_left₀ hexp1_gt (by norm_num) (by decide))
    have h := Real.log_lt_log (by norm_num) hp
    rw [← Real.exp_nat_mul, Real.log_exp] at h; push_cast at h; linarith
  have hX_eq : utX n = (283 * 10 ^ 8 : ℝ) * u := by dsimp [u]; ring
  have hlogX_u : Real.log (utX n) < 25 + Real.log u := by
    rw [hX_eq, Real.log_mul (by norm_num) hu_pos.ne']
    linarith
  have hH_le_75 : (H : ℝ) ≤ 75 * (1 + Real.log u / 5) := by linarith
  have hu_pow5 : (1 + Real.log u / 5) ^ 5 ≤ u := pow_one_add_log_div_le hu1 5 (by decide)
  have hH5 : (H : ℝ) ^ 5 ≤ (75 : ℝ) ^ 5 * u := by
    have h1 : (H : ℝ) ^ 5 ≤ (75 * (1 + Real.log u / 5)) ^ 5 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hH_le_75 5
    have h2 : (75 * (1 + Real.log u / 5)) ^ 5 = (75 : ℝ) ^ 5 * (1 + Real.log u / 5) ^ 5 := by ring
    exact h1.trans (h2 ▸ mul_le_mul_of_nonneg_left hu_pow5 (by norm_num))
  have hp_pos : (0 : ℝ) < (2 * p : ℝ) := by exact_mod_cast (show 0 < 2 * p by omega)
  have hp_le_H : (p : ℝ) ≤ (H : ℝ) := by exact_mod_cast hpH
  have hH_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
  have hy_lo : ((3 / 10000 : ℝ) * utX n) / (H : ℝ) ≤ (c - b) / (2 * p) := by
    have h1 : ((6 / 10000 : ℝ) * utX n) / (2 * (H : ℝ)) ≤ (c - b) / (2 * (p : ℝ)) :=
      (div_le_div_of_nonneg_right hw (by positivity)).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith))
    have h2 : ((6 / 10000 : ℝ) * utX n) / (2 * (H : ℝ)) = ((3 / 10000 : ℝ) * utX n) / (H : ℝ) := by ring
    linarith
  apply exp_two_fifths_log_le_of_pow hb_pos (by positivity)
  have hb_le_X : b ≤ utX n := hb_le_c.trans hc_le
  have hb2 : b ^ 2 ≤ (utX n) ^ 2 := pow_le_pow_left₀ hb_pos.le hb_le_X 2
  have hpow5_lo : (((3 / 10000 : ℝ) * utX n) / (H : ℝ)) ^ 5 ≤ ((c - b) / (2 * p)) ^ 5 :=
    pow_le_pow_left₀ (by positivity) hy_lo 5
  refine hb2.trans (le_trans ?_ hpow5_lo)
  rw [div_pow, le_div_iff₀ (pow_pos hH_pos 5)]
  have hmul : (utX n) ^ 2 * (H : ℝ) ^ 5 ≤ (utX n) ^ 2 * ((75 : ℝ) ^ 5 * u) :=
    mul_le_mul_of_nonneg_left hH5 (sq_nonneg _)
  refine hmul.trans ?_
  rw [hX_eq]
  have hu3 : u ≤ u ^ 3 := by nlinarith [sq_nonneg (u - 1)]
  have hcoef : (283 * 10 ^ 8 : ℝ) ^ 2 * (75 : ℝ) ^ 5 ≤
      (3 / 10000 : ℝ) ^ 5 * (283 * 10 ^ 8 : ℝ) ^ 5 := by norm_num
  have hprod_u : ((283 * 10 ^ 8 : ℝ) ^ 2 * (75 : ℝ) ^ 5) * u ^ 3 ≤
      ((3 / 10000 : ℝ) ^ 5 * (283 * 10 ^ 8 : ℝ) ^ 5) * u ^ 5 := by
    have hu3_5 : u ^ 3 ≤ u ^ 5 := by nlinarith [pow_pos hu_pos 3, sq_nonneg (u - 1)]
    exact mul_le_mul hcoef hu3_5 (by positivity) (by positivity)
  calc
    ((283 * 10 ^ 8 : ℝ) * u) ^ 2 * ((75 : ℝ) ^ 5 * u)
        = ((283 * 10 ^ 8 : ℝ) ^ 2 * (75 : ℝ) ^ 5) * u ^ 3 := by ring
    _ ≤ ((3 / 10000 : ℝ) ^ 5 * (283 * 10 ^ 8 : ℝ) ^ 5) * u ^ 5 := hprod_u
    _ = ((3 / 10000 : ℝ) * ((283 * 10 ^ 8 : ℝ) * u)) ^ 5 := by ring

/-- Supply and majority-coloring cap for every ordinary `ModCover` bin `j < 54`
and every prime `p ≤ utH0Max n`: there exists `M` bounding all mod-`2p` color classes
with `M + 2 * utModRounds n * (6 * n) ≤ (apInterval (utModBinLo n j) (utModBinHi n j) 2 1).card`. -/
theorem ut_mod_bin_supply
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports) (mv : MVBrunTitchmarsh)
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n j : ℕ} (hn : 35735 ≤ n) (hj : j < 54) :
    ∃ M : ℕ,
      M + 2 * utModRounds n * (6 * n) ≤ (apInterval (utModBinLo n j) (utModBinHi n j) 2 1).card ∧
      ∀ (p r : ℕ), Nat.Prime p → p ≤ utH0Max n →
        ((apInterval (utModBinLo n j) (utModBinHi n j) 2 1).filter (fun x => x % (2 * p) = r)).card ≤ M := by
  obtain ⟨hlog24, _, hLn11, _, _, hY_gt, _, _, _, _⟩ :=
    ut_sharp_scale_bounds rs lower sharp upper hn
  obtain ⟨hle95, hge95, _, _⟩ := ut_ln14_step_bounds rs lower sharp upper hn
  obtain ⟨_, hX_283, _, _, _⟩ := poolMaximum_bounds_ge_35735 sharp upper hn
  have hX : (283 * 10 ^ 8 : ℝ) ≤ utX n := by dsimp [utX]; linarith
  have hX_pos : 0 < utX n := by linarith
  have hlog_pos : 0 < Real.log (utX n) := by linarith
  have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  let b := utModBinLo n j
  let c := utModBinHi n j
  have hj_le : (j : ℝ) ≤ 53 := by exact_mod_cast (show j ≤ 53 by omega)
  have hj_nn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hb_ge : (852 / 1000 : ℝ) * utX n ≤ b := by
    dsimp [b, utModBinLo]; nlinarith
  have hc_le : c ≤ (9168 / 10000 : ℝ) * utX n := by
    dsimp [c, utModBinHi]; nlinarith
  have hcb_eq : c - b = (12 / 10000 : ℝ) * utX n := by
    dsimp [b, c, utModBinLo, utModBinHi]; ring
  have hb_9e9 : (9 * 10 ^ 9 : ℝ) ≤ b := by linarith
  have hbc : b < c := by rw [← sub_pos, hcb_eq]; positivity
  have hcard := apInterval_mod_two_card_lower_ge_9e9 bmor imp
    (b := b) (c := c) (X := utX n) hb_9e9 hbc.le (by linarith)
  have hlog_852 : -(1 / 5 : ℝ) < Real.log (852 / 1000 : ℝ) := by
    have hp : Real.exp (-(1 / 5 : ℝ)) < 852 / 1000 := by
      have h1 : (Real.exp (-(1 / 5 : ℝ))) ^ 5 = (Real.exp 1)⁻¹ := by
        rw [← Real.exp_nat_mul]
        have : ((5 : ℕ) : ℝ) * (-(1 / 5 : ℝ)) = -1 := by norm_num
        rw [this, Real.exp_neg]
      have h2 : (Real.exp 1)⁻¹ < (27182 / 10000 : ℝ)⁻¹ :=
        inv_strictAnti₀ (by norm_num) (lt_trans (by norm_num) Real.exp_one_gt_d9)
      have h3 : (27182 / 10000 : ℝ)⁻¹ < (852 / 1000 : ℝ) ^ 5 := by norm_num
      exact (pow_lt_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by decide : 5 ≠ 0)).mp
        (by rw [h1]; exact h2.trans h3)
    have h := Real.log_lt_log (Real.exp_pos _) hp
    rwa [Real.log_exp] at h
  have hlog_b_ge : (119 / 120 : ℝ) * Real.log (utX n) ≤ Real.log b := by
    have h1 := Real.log_le_log (by positivity) hb_ge
    rw [Real.log_mul (by norm_num) hX_pos.ne'] at h1
    linarith
  let M_real : ℝ := ((c - b) / 2 + (b + c) / 25000) / Real.log b
  have hM_nn : 0 ≤ M_real := by
    dsimp [M_real]
    have : 0 < Real.log b := by linarith
    have : 0 ≤ b := by linarith
    have : 0 ≤ c := by linarith
    have : 0 ≤ c - b := by linarith
    positivity
  refine ⟨⌊M_real⌋₊, ?_, ?_⟩
  · have hM_ub : M_real ≤ (680 / 1000000 : ℝ) * utY n := by
      dsimp [M_real, utY]
      have hnum : (c - b) / 2 + (b + c) / 25000 ≤ (6735 / 10000000 : ℝ) * utX n := by
        rw [hcb_eq]; linarith
      have h1 : ((c - b) / 2 + (b + c) / 25000) / Real.log b ≤
          ((6735 / 10000000 : ℝ) * utX n) / ((119 / 120 : ℝ) * Real.log (utX n)) :=
        (div_le_div_of_nonneg_right hnum (by linarith)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hlog_b_ge)
      have h2 : ((6735 / 10000000 : ℝ) * utX n) / ((119 / 120 : ℝ) * Real.log (utX n)) ≤
          (680 / 1000000 : ℝ) * (utX n / Real.log (utX n)) := by
        have hrew : ((6735 / 10000000 : ℝ) * utX n) / ((119 / 120 : ℝ) * Real.log (utX n)) =
            ((6735 / 10000000 : ℝ) / (119 / 120 : ℝ)) * (utX n / Real.log (utX n)) := by ring
        rw [hrew]
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      exact h1.trans h2
    have hcard_lo : (1116 / 1000000 : ℝ) * utY n ≤
        ((c - b) - (b + c) / 22000) / Real.log (utX n) := by
      dsimp [utY]
      rw [mul_div_assoc', hcb_eq]
      exact div_le_div_of_nonneg_right (by linarith) hlog_pos.le
    have hneed : (2 * utModRounds n * (6 * n) : ℝ) < (436 / 1000000 : ℝ) * utY n := by
      by_cases hn95 : n ≤ 95000
      · have hLn13 := hle95 hn95
        have hrnd1 : utModRounds n = 1 := by
          dsimp [utModRounds, utH0Max]; omega
        rw [show (utModRounds n : ℝ) = 1 by exact_mod_cast hrnd1]
        nlinarith
      · have hn95' : 95000 ≤ n := by omega
        obtain ⟨hlin95, _⟩ := hge95 hn95'
        have hn95R : (95000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn95'
        have hrnd_le : (utModRounds n : ℝ) ≤ (1 / 100000 : ℝ) * (n : ℝ) + 4 / 3 := by
          have hdiv : utModRounds n * 54 ≤ 3 * utLn n + 68 := by
            dsimp [utModRounds, utH0Max]; omega
          have hdivR : (utModRounds n : ℝ) * 54 ≤ 3 * (utLn n : ℝ) + 68 := by exact_mod_cast hdiv
          linarith
        nlinarith
    have hfl : (⌊M_real⌋₊ : ℝ) ≤ M_real := Nat.floor_le hM_nn
    have hsum_lt : ((⌊M_real⌋₊ + 2 * utModRounds n * (6 * n) : ℕ) : ℝ) <
        ((apInterval b c 2 1).card : ℝ) := by
      push_cast; linarith
    exact_mod_cast hsum_lt.le
  · intro p r hp hpH
    have hexp := ut_mod_sharp_exp_gate rs lower sharp upper hn hp.two_le hpH
      (by linarith) (hc_le.trans (by linarith)) hbc.le (by rw [hcb_eq]; linarith)
    have hp_lt_b : (p : ℝ) < b := by
      have hp_le_H : (p : ℝ) ≤ (utH0Max n : ℝ) := by exact_mod_cast hpH
      have hH_le_log : (utH0Max n : ℝ) ≤ 3 * Real.log (utX n) := by
        have hlog_lo := (ut_sharp_scale_bounds rs lower sharp upper hn).2.2.2.1
        have : (utH0Max n : ℝ) = 3 * ((utLn n : ℝ) + 5) := by dsimp [utH0Max]; push_cast; ring
        linarith
      have hlog_small : Real.log (utX n) ≤ 10 + utX n / 1024 := by
        have h1 : utX n = (2 : ℝ) ^ 10 * (utX n / 1024) := by ring
        have h2 := Real.log_le_sub_one_of_pos (by positivity : 0 < utX n / 1024)
        have h3 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
        rw [h1, Real.log_mul (by positivity) (by positivity), Real.log_pow]
        push_cast; linarith
      linarith
    have hsharp := apInterval_filter_mod_two_prime_sharp bmor imp mv (b := b) (c := c) (r := r)
      hp (by linarith) hbc hp_lt_b hexp
    exact Nat.le_floor hsharp

/-- Diagonal `ModCover` supply on bin `54` (`j = 54`), split into left half
`(utModBinLo n 54, utModBinMid n 54]` and right half `(utModBinMid n 54, utModBinHi n 54]`,
for product-bin incongruent `DoublePair` pigeonhole across all `2 * (h0 - 1)` diagonal switches. -/
theorem ut_mod_diag_half_bin_supply
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports) (mv : MVBrunTitchmarsh)
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n : ℕ} (hn : 35735 ≤ n) :
    let S_A := apInterval (utModBinLo n 54) (utModBinMid n 54) 2 1
    let S_B := apInterval (utModBinMid n 54) (utModBinHi n 54) 2 1
    ∃ M_B : ℕ,
      4 * utH0Max n < S_A.card ∧
      M_B + 4 * utH0Max n < S_B.card ∧
      ⌊utModBinHi n 54 - utModBinLo n 54⌋₊ + 1 <
        (S_A.card - 4 * utH0Max n) * (S_B.card - 4 * utH0Max n - M_B) ∧
      ∀ (p r : ℕ), Nat.Prime p → p ≤ utH0Max n →
        (S_B.filter (fun x => x % (2 * p) = r)).card ≤ M_B := by
  dsimp only
  obtain ⟨hlog24, _, _, _, hlog_hi, hY_gt, _, _, hLn_lin, _⟩ :=
    ut_sharp_scale_bounds rs lower sharp upper hn
  obtain ⟨_, hX_283, _, _, _⟩ := poolMaximum_bounds_ge_35735 sharp upper hn
  have hX : (283 * 10 ^ 8 : ℝ) ≤ utX n := by dsimp [utX]; linarith
  have hX_pos : 0 < utX n := by linarith
  have hlog_pos : 0 < Real.log (utX n) := by linarith
  have hYX : utY n * Real.log (utX n) = utX n := div_mul_cancel₀ _ hlog_pos.ne'
  have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  let bA := utModBinLo n 54
  let m54 := utModBinMid n 54
  let cB := utModBinHi n 54
  have hbA_eq : bA = (9168 / 10000 : ℝ) * utX n := by dsimp [bA, utModBinLo]; ring
  have hm54_eq : m54 = (9174 / 10000 : ℝ) * utX n := by dsimp [m54, utModBinMid]; ring
  have hcB_eq : cB = (9180 / 10000 : ℝ) * utX n := by dsimp [cB, utModBinHi]; ring
  have hcardA := apInterval_mod_two_card_lower_ge_9e9 bmor imp
    (b := bA) (c := m54) (X := utX n) (by linarith) (by linarith) (by linarith)
  have hcardB := apInterval_mod_two_card_lower_ge_9e9 bmor imp
    (b := m54) (c := cB) (X := utX n) (by linarith) (by linarith) (by linarith)
  have hcardA_lo : (516 / 1000000 : ℝ) * utY n ≤ ((apInterval bA m54 2 1).card : ℝ) := by
    refine le_trans ?_ hcardA
    dsimp [utY]; rw [mul_div_assoc', hbA_eq, hm54_eq]
    exact div_le_div_of_nonneg_right (by linarith) hlog_pos.le
  have hcardB_lo : (516 / 1000000 : ℝ) * utY n ≤ ((apInterval m54 cB 2 1).card : ℝ) := by
    refine le_trans ?_ hcardB
    dsimp [utY]; rw [mul_div_assoc', hm54_eq, hcB_eq]
    exact div_le_div_of_nonneg_right (by linarith) hlog_pos.le
  have hlog_9174 : -(1 / 5 : ℝ) < Real.log (9174 / 10000 : ℝ) := by
    have hp : Real.exp (-(1 / 5 : ℝ)) < 9174 / 10000 := by
      have h1 : (Real.exp (-(1 / 5 : ℝ))) ^ 5 = (Real.exp 1)⁻¹ := by
        rw [← Real.exp_nat_mul]
        have : ((5 : ℕ) : ℝ) * (-(1 / 5 : ℝ)) = -1 := by norm_num
        rw [this, Real.exp_neg]
      have h2 : (Real.exp 1)⁻¹ < (27182 / 10000 : ℝ)⁻¹ :=
        inv_strictAnti₀ (by norm_num) (lt_trans (by norm_num) Real.exp_one_gt_d9)
      have h3 : (27182 / 10000 : ℝ)⁻¹ < (9174 / 10000 : ℝ) ^ 5 := by norm_num
      exact (pow_lt_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by decide : 5 ≠ 0)).mp
        (by rw [h1]; exact h2.trans h3)
    have h := Real.log_lt_log (Real.exp_pos _) hp
    rwa [Real.log_exp] at h
  have hlog_m_ge : (119 / 120 : ℝ) * Real.log (utX n) ≤ Real.log m54 := by
    have h1 := Real.log_le_log (by positivity) (le_of_eq hm54_eq.symm)
    rw [Real.log_mul (by norm_num) hX_pos.ne'] at h1
    linarith
  let M_real : ℝ := ((cB - m54) / 2 + (m54 + cB) / 25000) / Real.log m54
  have hM_nn : 0 ≤ M_real := by
    dsimp [M_real]
    have : 0 < Real.log m54 := by linarith
    have : 0 ≤ m54 := by linarith
    have : 0 ≤ cB := by linarith
    have : 0 ≤ cB - m54 := by linarith
    positivity
  have hM_ub : M_real ≤ (378 / 1000000 : ℝ) * utY n := by
    dsimp [M_real, utY]
    have hnum : (cB - m54) / 2 + (m54 + cB) / 25000 ≤ (3735 / 10000000 : ℝ) * utX n := by
      rw [hm54_eq, hcB_eq]; linarith
    have h1 : ((cB - m54) / 2 + (m54 + cB) / 25000) / Real.log m54 ≤
        ((3735 / 10000000 : ℝ) * utX n) / ((119 / 120 : ℝ) * Real.log (utX n)) :=
      (div_le_div_of_nonneg_right hnum (by linarith)).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hlog_m_ge)
    have h2 : ((3735 / 10000000 : ℝ) * utX n) / ((119 / 120 : ℝ) * Real.log (utX n)) ≤
        (378 / 1000000 : ℝ) * (utX n / Real.log (utX n)) := by
      have hrew : ((3735 / 10000000 : ℝ) * utX n) / ((119 / 120 : ℝ) * Real.log (utX n)) =
          ((3735 / 10000000 : ℝ) / (119 / 120 : ℝ)) * (utX n / Real.log (utX n)) := by ring
      rw [hrew]
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    exact h1.trans h2
  have h4H_ub : (4 * utH0Max n : ℝ) ≤ (16 / 1000000 : ℝ) * utY n := by
    have : (utH0Max n : ℝ) = 3 * ((utLn n : ℝ) + 5) := by dsimp [utH0Max]; push_cast; ring
    nlinarith
  have hfl : (⌊M_real⌋₊ : ℝ) ≤ M_real := Nat.floor_le hM_nn
  have hA_gt : 4 * utH0Max n < (apInterval bA m54 2 1).card := by
    have hlt : ((4 * utH0Max n : ℕ) : ℝ) < ((apInterval bA m54 2 1).card : ℝ) := by
      push_cast; nlinarith
    exact_mod_cast hlt
  have hB_gt : ⌊M_real⌋₊ + 4 * utH0Max n < (apInterval m54 cB 2 1).card := by
    have hlt : ((⌊M_real⌋₊ + 4 * utH0Max n : ℕ) : ℝ) < ((apInterval m54 cB 2 1).card : ℝ) := by
      push_cast; nlinarith
    exact_mod_cast hlt
  refine ⟨⌊M_real⌋₊, hA_gt, hB_gt, ?_, ?_⟩
  · have hremA : (490 / 1000000 : ℝ) * utY n ≤
        (((apInterval bA m54 2 1).card - 4 * utH0Max n : ℕ) : ℝ) := by
      rw [Nat.cast_sub hA_gt.le]; push_cast; linarith
    have hremB : (120 / 1000000 : ℝ) * utY n ≤
        (((apInterval m54 cB 2 1).card - 4 * utH0Max n - ⌊M_real⌋₊ : ℕ) : ℝ) := by
      have h1 : 4 * utH0Max n ≤ (apInterval m54 cB 2 1).card := by omega
      have h2 : ⌊M_real⌋₊ ≤ (apInterval m54 cB 2 1).card - 4 * utH0Max n := by omega
      rw [Nat.cast_sub h2, Nat.cast_sub h1]; push_cast; nlinarith
    have hY2_X : 3 * 10 ^ 7 * utX n < (utY n) ^ 2 := by
      have hlog_ub_n : Real.log (utX n) < (1 / 1000 : ℝ) * (n : ℝ) := by linarith
      have hY_pos : 0 < utY n := by nlinarith
      have hX_ub : utX n < (1 / 1000 : ℝ) * (n : ℝ) * utY n := by
        rw [← hYX]
        have hm := mul_lt_mul_of_pos_right hlog_ub_n hY_pos
        linarith
      nlinarith
    have hprod_lo : ((490 / 1000000 : ℝ) * utY n) * ((120 / 1000000 : ℝ) * utY n) ≤
        ((((apInterval bA m54 2 1).card - 4 * utH0Max n) *
          ((apInterval m54 cB 2 1).card - 4 * utH0Max n - ⌊M_real⌋₊) : ℕ) : ℝ) := by
      push_cast; exact mul_le_mul hremA hremB (by nlinarith) (by positivity)
    have hspan_ub : ((⌊cB - bA⌋₊ + 1 : ℕ) : ℝ) ≤ (12 / 10000 : ℝ) * utX n + 1 := by
      push_cast
      have h1 : (⌊cB - bA⌋₊ : ℝ) ≤ cB - bA := Nat.floor_le (by linarith)
      linarith
    have hlt_R : ((⌊cB - bA⌋₊ + 1 : ℕ) : ℝ) <
        ((((apInterval bA m54 2 1).card - 4 * utH0Max n) *
          ((apInterval m54 cB 2 1).card - 4 * utH0Max n - ⌊M_real⌋₊) : ℕ) : ℝ) := by
      nlinarith
    exact_mod_cast hlt_R
  · intro p r hp hpH
    have hexp := ut_mod_sharp_exp_gate rs lower sharp upper (b := m54) (c := cB) hn hp.two_le hpH
      (by linarith) (by linarith) (by linarith) (by linarith)
    have hp_lt_m : (p : ℝ) < m54 := by
      have hp_le_H : (p : ℝ) ≤ (utH0Max n : ℝ) := by exact_mod_cast hpH
      have hH_le_log : (utH0Max n : ℝ) ≤ 3 * Real.log (utX n) := by
        have hlog_lo := (ut_sharp_scale_bounds rs lower sharp upper hn).2.2.2.1
        have : (utH0Max n : ℝ) = 3 * ((utLn n : ℝ) + 5) := by dsimp [utH0Max]; push_cast; ring
        linarith
      have hlog_small : Real.log (utX n) ≤ 10 + utX n / 1024 := by
        have h1 : utX n = (2 : ℝ) ^ 10 * (utX n / 1024) := by ring
        have h2 := Real.log_le_sub_one_of_pos (by positivity : 0 < utX n / 1024)
        have h3 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
        rw [h1, Real.log_mul (by positivity) (by positivity), Real.log_pow]
        push_cast; linarith
      linarith
    have hsharp := apInterval_filter_mod_two_prime_sharp bmor imp mv (b := m54) (c := cB) (r := r) hp
      (by linarith) (by linarith) hp_lt_m hexp
    exact Nat.le_floor hsharp

/-- Supply for every Doubling stage `k : Fin 10` (`utDblLow` and `utDblHigh`), covering both
`6 * n` ordinary pairs and product-bin pigeonhole for `2` diagonal `DoublePair`s. -/
theorem ut_dbl_bin_supply
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n : ℕ} (hn : 35735 ≤ n) (k : Fin 10) :
    let S_lo := apInterval (utDblLowLo n k) (utDblLowHi n k) 2 1
    let S_hi := apInterval (utDblHighLo n k) (utDblHighHi n k) 2 1
    6 * n + 4 < S_lo.card ∧
    6 * n + 4 < S_hi.card ∧
    ⌊utX n⌋₊ + 1 < (S_lo.card - (6 * n + 4)) * (S_hi.card - (6 * n + 4)) := by
  dsimp only
  obtain ⟨_, _, _, _, hlog_hi, hY_gt, _, _, hLn_lin, _⟩ :=
    ut_sharp_scale_bounds rs lower sharp upper hn
  obtain ⟨_, hX_283, _, _, _⟩ := poolMaximum_bounds_ge_35735 sharp upper hn
  obtain ⟨hlow_ge, hlt_lh, hhigh_le, _⟩ := ut_dbl_frac_recurrence.1 k
  have hX : (283 * 10 ^ 8 : ℝ) ≤ utX n := by dsimp [utX]; linarith
  have hX_pos : 0 < utX n := by linarith
  have hlog_pos : 0 < Real.log (utX n) := by linarith
  have hYX : utY n * Real.log (utX n) = utX n := div_mul_cancel₀ _ hlog_pos.ne'
  have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hblo_9e9 : (9 * 10 ^ 9 : ℝ) ≤ utDblLowLo n k := by
    dsimp [utDblLowLo]; nlinarith
  have hbhi_9e9 : (9 * 10 ^ 9 : ℝ) ≤ utDblHighLo n k := by
    dsimp [utDblHighLo]; nlinarith
  have hclo_X : utDblLowHi n k ≤ utX n := by dsimp [utDblLowHi]; nlinarith
  have hchi_X : utDblHighHi n k ≤ utX n := by dsimp [utDblHighHi]; nlinarith
  have hcard_lo := apInterval_mod_two_card_lower_ge_9e9 bmor imp hblo_9e9
    (by dsimp [utDblLowLo, utDblLowHi]; nlinarith) hclo_X
  have hcard_hi := apInterval_mod_two_card_lower_ge_9e9 bmor imp hbhi_9e9
    (by dsimp [utDblHighLo, utDblHighHi]; nlinarith) hchi_X
  have hlo_ge : (914 / 1000000 : ℝ) * utY n ≤ ((apInterval (utDblLowLo n k) (utDblLowHi n k) 2 1).card : ℝ) := by
    refine le_trans ?_ hcard_lo
    dsimp [utY, utDblLowLo, utDblLowHi]; rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by nlinarith) hlog_pos.le
  have hhi_ge : (914 / 1000000 : ℝ) * utY n ≤ ((apInterval (utDblHighLo n k) (utDblHighHi n k) 2 1).card : ℝ) := by
    refine le_trans ?_ hcard_hi
    dsimp [utY, utDblHighLo, utDblHighHi]; rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by nlinarith) hlog_pos.le
  have h6n_ub : ((6 * n + 4 : ℕ) : ℝ) < (200 / 1000000 : ℝ) * utY n := by
    push_cast; nlinarith
  have hgt_lo : 6 * n + 4 < (apInterval (utDblLowLo n k) (utDblLowHi n k) 2 1).card := by
    have hlt : ((6 * n + 4 : ℕ) : ℝ) < ((apInterval (utDblLowLo n k) (utDblLowHi n k) 2 1).card : ℝ) := by
      nlinarith
    exact_mod_cast hlt
  have hgt_hi : 6 * n + 4 < (apInterval (utDblHighLo n k) (utDblHighHi n k) 2 1).card := by
    have hlt : ((6 * n + 4 : ℕ) : ℝ) < ((apInterval (utDblHighLo n k) (utDblHighHi n k) 2 1).card : ℝ) := by
      nlinarith
    exact_mod_cast hlt
  refine ⟨hgt_lo, hgt_hi, ?_⟩
  have hrem_lo : (7 / 10000 : ℝ) * utY n ≤
      (((apInterval (utDblLowLo n k) (utDblLowHi n k) 2 1).card - (6 * n + 4) : ℕ) : ℝ) := by
    rw [Nat.cast_sub hgt_lo.le]; linarith
  have hrem_hi : (7 / 10000 : ℝ) * utY n ≤
      (((apInterval (utDblHighLo n k) (utDblHighHi n k) 2 1).card - (6 * n + 4) : ℕ) : ℝ) := by
    rw [Nat.cast_sub hgt_hi.le]; linarith
  have hY2_X : 3 * 10 ^ 7 * utX n < (utY n) ^ 2 := by
    have hlog_ub_n : Real.log (utX n) < (1 / 1000 : ℝ) * (n : ℝ) := by linarith
    have hY_pos : 0 < utY n := by nlinarith
    have hX_ub : utX n < (1 / 1000 : ℝ) * (n : ℝ) * utY n := by
      rw [← hYX]
      have hm := mul_lt_mul_of_pos_right hlog_ub_n hY_pos
      linarith
    nlinarith
  have hprod : ((7 / 10000 : ℝ) * utY n) * ((7 / 10000 : ℝ) * utY n) ≤
      ((((apInterval (utDblLowLo n k) (utDblLowHi n k) 2 1).card - (6 * n + 4)) *
        ((apInterval (utDblHighLo n k) (utDblHighHi n k) 2 1).card - (6 * n + 4)) : ℕ) : ℝ) := by
    push_cast; exact mul_le_mul hrem_lo hrem_hi (by nlinarith) (by positivity)
  have hfl_X : ((⌊utX n⌋₊ + 1 : ℕ) : ℝ) ≤ utX n + 1 := by
    push_cast; linarith [Nat.floor_le hX_pos.le]
  have hlt_R : ((⌊utX n⌋₊ + 1 : ℕ) : ℝ) <
      ((((apInterval (utDblLowLo n k) (utDblLowHi n k) 2 1).card - (6 * n + 4)) *
        ((apInterval (utDblHighLo n k) (utDblHighHi n k) 2 1).card - (6 * n + 4)) : ℕ) : ℝ) := by
    nlinarith
  exact_mod_cast hlt_R

/-- Maximum ordinary wide stages assigned to a single `WideLow`/`WideHigh` bin `m < 30`. -/
def utWideOrdPerBin (n : ℕ) : ℕ := (utWOrd n + 29) / 30

/-- Maximum diagonal wide stage pairs assigned to a single `WideLow`/`WideHigh` bin `m < 30`. -/
def utWideDiagPerBin (n : ℕ) : ℕ := (utWDiag n + 29) / 30

/-- Supply for every `WideLow`/`WideHigh` bin pair `m < 30`, covering `utWideOrdPerBin n`
ordinary wide stages (`6 * n` pairs each) and `utWideDiagPerBin n` pairs of diagonal `DoublePair`s. -/
theorem ut_wide_bin_supply
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n m : ℕ} (hn : 35735 ≤ n) (hm : m < 30) :
    let S_lo := apInterval (utWideLowLo n m) (utWideLowHi n m) 2 1
    let S_hi := apInterval (utWideHighLo n m) (utWideHighHi n m) 2 1
    let U := 6 * n * utWideOrdPerBin n + 4 * utWideDiagPerBin n
    U < S_lo.card ∧
    U < S_hi.card ∧
    ⌊utX n⌋₊ + 1 < (S_lo.card - U) * (S_hi.card - U) := by
  dsimp only
  obtain ⟨_, _, _, _, hlog_hi, hY_gt, _, _, hLn_lin, _⟩ :=
    ut_sharp_scale_bounds rs lower sharp upper hn
  obtain ⟨_, hX_283, _, _, _⟩ := poolMaximum_bounds_ge_35735 sharp upper hn
  have hX : (283 * 10 ^ 8 : ℝ) ≤ utX n := by dsimp [utX]; linarith
  have hX_pos : 0 < utX n := by linarith
  have hlog_pos : 0 < Real.log (utX n) := by linarith
  have hYX : utY n * Real.log (utX n) = utX n := div_mul_cancel₀ _ hlog_pos.ne'
  have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hm_le : (m : ℝ) ≤ 29 := by exact_mod_cast (show m ≤ 29 by omega)
  have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hcard_lo := apInterval_mod_two_card_lower_ge_1e8 bmor imp
    (b := utWideLowLo n m) (c := utWideLowHi n m) (X := utX n)
    (by dsimp [utWideLowLo]; nlinarith)
    (by dsimp [utWideLowLo, utWideLowHi]; nlinarith)
    (by dsimp [utWideLowHi]; nlinarith)
  have hcard_hi := apInterval_mod_two_card_lower_ge_2e10 bmor imp
    (b := utWideHighLo n m) (c := utWideHighHi n m) (X := utX n)
    (by dsimp [utWideHighLo]; nlinarith)
    (by dsimp [utWideHighLo, utWideHighHi]; nlinarith)
    (by dsimp [utWideHighHi]; nlinarith)
  have hlo_ge : (194 / 100000 : ℝ) * utY n ≤ ((apInterval (utWideLowLo n m) (utWideLowHi n m) 2 1).card : ℝ) := by
    refine le_trans ?_ hcard_lo
    dsimp [utY, utWideLowLo, utWideLowHi]; rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by nlinarith) hlog_pos.le
  have hhi_ge : (191 / 100000 : ℝ) * utY n ≤ ((apInterval (utWideHighLo n m) (utWideHighHi n m) 2 1).card : ℝ) := by
    refine le_trans ?_ hcard_hi
    dsimp [utY, utWideHighLo, utWideHighHi]; rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by nlinarith) hlog_pos.le
  have hW_ord_ub : (utWideOrdPerBin n : ℝ) ≤ (n : ℝ) / 12900 + 3 / 2 := by
    have h1 : utWideOrdPerBin n * 12900 ≤ n + 17630 := by
      dsimp [utWideOrdPerBin, utWOrd]; omega
    have h1R : (utWideOrdPerBin n : ℝ) * 12900 ≤ (n : ℝ) + 17630 := by exact_mod_cast h1
    linarith
  have hW_diag_ub : (utWideDiagPerBin n : ℝ) ≤ (n : ℝ) / 60000 + (utLn n : ℝ) / 30 + 1 := by
    have h1 : utWideDiagPerBin n * 60000 ≤ n + 2000 * utLn n + 58000 := by
      dsimp [utWideDiagPerBin, utWDiag]; omega
    have h1R : (utWideDiagPerBin n : ℝ) * 60000 ≤ (n : ℝ) + 2000 * (utLn n : ℝ) + 58000 := by
      exact_mod_cast h1
    linarith
  let U := 6 * n * utWideOrdPerBin n + 4 * utWideDiagPerBin n
  have hU_ub : (U : ℝ) < (100 / 100000 : ℝ) * utY n := by
    dsimp [U]; push_cast; nlinarith
  have hgt_lo : U < (apInterval (utWideLowLo n m) (utWideLowHi n m) 2 1).card := by
    have hlt : (U : ℝ) < ((apInterval (utWideLowLo n m) (utWideLowHi n m) 2 1).card : ℝ) := by
      nlinarith
    exact_mod_cast hlt
  have hgt_hi : U < (apInterval (utWideHighLo n m) (utWideHighHi n m) 2 1).card := by
    have hlt : (U : ℝ) < ((apInterval (utWideHighLo n m) (utWideHighHi n m) 2 1).card : ℝ) := by
      nlinarith
    exact_mod_cast hlt
  refine ⟨hgt_lo, hgt_hi, ?_⟩
  have hrem_lo : (9 / 10000 : ℝ) * utY n ≤
      (((apInterval (utWideLowLo n m) (utWideLowHi n m) 2 1).card - U : ℕ) : ℝ) := by
    rw [Nat.cast_sub hgt_lo.le]; linarith
  have hrem_hi : (9 / 10000 : ℝ) * utY n ≤
      (((apInterval (utWideHighLo n m) (utWideHighHi n m) 2 1).card - U : ℕ) : ℝ) := by
    rw [Nat.cast_sub hgt_hi.le]; linarith
  have hY2_X : 3 * 10 ^ 7 * utX n < (utY n) ^ 2 := by
    have hlog_ub_n : Real.log (utX n) < (1 / 1000 : ℝ) * (n : ℝ) := by linarith
    have hY_pos : 0 < utY n := by nlinarith
    have hX_ub : utX n < (1 / 1000 : ℝ) * (n : ℝ) * utY n := by
      rw [← hYX]
      have hm := mul_lt_mul_of_pos_right hlog_ub_n hY_pos
      linarith
    nlinarith
  have hprod : ((9 / 10000 : ℝ) * utY n) * ((9 / 10000 : ℝ) * utY n) ≤
      ((((apInterval (utWideLowLo n m) (utWideLowHi n m) 2 1).card - U) *
        ((apInterval (utWideHighLo n m) (utWideHighHi n m) 2 1).card - U) : ℕ) : ℝ) := by
    push_cast; exact mul_le_mul hrem_lo hrem_hi (by nlinarith) (by positivity)
  have hfl_X : ((⌊utX n⌋₊ + 1 : ℕ) : ℝ) ≤ utX n + 1 := by
    push_cast; linarith [Nat.floor_le hX_pos.le]
  have hlt_R : ((⌊utX n⌋₊ + 1 : ℕ) : ℝ) <
      ((((apInterval (utWideLowLo n m) (utWideLowHi n m) 2 1).card - U) *
        ((apInterval (utWideHighLo n m) (utWideHighHi n m) 2 1).card - U) : ℕ) : ℝ) := by
    nlinarith
  exact_mod_cast hlt_R

/-- Geometric layer/rectangle packing gates across all `n ≥ 35,735`. -/
theorem ut_packing_and_keepout_gates
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n S_ord L_diag : ℕ} (hn : 35735 ≤ n)
    (hS : S_ord ≤ utSeedStages n + utStepsAP n + utStepsMV n + utStepsBoost n + utH0Max n + 10 + utWOrd n)
    (hL : L_diag ≤ 2 * (utSeedStages n + utStepsAP n + utStepsMV n + utStepsBoost n + utH0Max n + 10 + utWDiag n)) :
    4 * (12 * S_ord + 4) + 8 < n ∧
    2 * L_diag + 1 ≤ n ∧
    4 * (12 * n * S_ord + 4 * L_diag) ≤ n * n := by
  obtain ⟨_, _, _, _, _, _, _, _, hLn_lin, _⟩ :=
    ut_sharp_scale_bounds rs lower sharp upper hn
  obtain ⟨_, _, _, hStot⟩ := ut_ln14_step_bounds rs lower sharp upper hn
  have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hSR : (S_ord : ℝ) ≤ (2075 / 100000 : ℝ) * (n : ℝ) :=
    (show (S_ord : ℝ) ≤ _ by exact_mod_cast hS).trans hStot
  have hLR : (L_diag : ℝ) ≤ 2 * ((2075 / 100000 : ℝ) * (n : ℝ) + (utLn n : ℝ)) := by
    have h1 : L_diag ≤ 2 * ((utSeedStages n + utStepsAP n + utStepsMV n + utStepsBoost n + utH0Max n + 10 + utWOrd n) + utLn n) := by
      dsimp [utWDiag, utWOrd] at hL ⊢; omega
    have h1R : (L_diag : ℝ) ≤ 2 * (((utSeedStages n + utStepsAP n + utStepsMV n + utStepsBoost n + utH0Max n + 10 + utWOrd n : ℕ) : ℝ) + (utLn n : ℝ)) := by
      exact_mod_cast h1
    linarith
  have h1 : 4 * (12 * S_ord + 4) + 8 < n := by
    have h25 : 48 * S_ord + 25 ≤ n := by
      have hR : ((48 * S_ord + 25 : ℕ) : ℝ) ≤ (n : ℝ) := by push_cast; linarith
      exact_mod_cast hR
    omega
  have h2 : 2 * L_diag + 1 ≤ n := by
    have hR : ((2 * L_diag + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by push_cast; linarith
    exact_mod_cast hR
  have h3 : 4 * (12 * n * S_ord + 4 * L_diag) ≤ n * n := by
    have hR : ((4 * (12 * n * S_ord + 4 * L_diag) : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by
      push_cast; nlinarith
    exact_mod_cast hR
  exact ⟨h1, h2, h3⟩

end

end Sude
