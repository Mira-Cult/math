import Sude.FWPoolBound
import Sude.BMORPoolCorrelatedMean
import Sude.LiBGCoarseBase

/-! Elementary bounds for the error terms in the FW mean comparison.
No new prime-counting input is introduced. -/

namespace Sude
noncomputable section

/-- Coarse error estimates for the actual pool. All quantities are explicit;
these inequalities alone do not establish the target mean interval. -/
theorem fw_mean_coarse_errors (lower : RSIndexLower) {n : ℕ}
    (hn : 19485 ≤ n) (hlog : 22 ≤ Real.log (poolMaximum n : ℝ)) :
    let N : ℝ := (n * n : ℕ)
    let X : ℝ := poolMaximum n
    let u : ℝ := Real.log X
    let q : ℝ := N / X
    let D : ℝ := (281649 / 62500 : ℝ) * (Real.sqrt X / u)
    let E : ℝ := (((poolMaximum n - 2 : ℕ) : ℝ) * D) / (N * X)
    let c : ℝ := (281649 / 62500 : ℝ) / 65536
    D * u / X ≤ c ∧ E ≤ D / N ∧
    (0 ≤ liFromTwo 4 ∧ liFromTwo 4 ≤ 4) ∧
    D / N + E ≤ 2 * c / (u * q) ∧
    liFromTwo 4 / (N * X) ≤ 4 * u / ((2 ^ 32 : ℝ)^2 * (u * q)) ∧
    bgLiUpperNorm u / N ≤ (1 + 1/u + 4/u^2) / ((2 ^ 32 : ℝ) * (u * q)) := by
  dsimp only
  let N : ℝ := (n * n : ℕ)
  let X : ℝ := poolMaximum n
  let u : ℝ := Real.log X
  let q : ℝ := N / X
  let D : ℝ := (281649 / 62500 : ℝ) * (Real.sqrt X / u)
  let E : ℝ := (((poolMaximum n - 2 : ℕ) : ℝ) * D) / (N * X)
  let c : ℝ := (281649 / 62500 : ℝ) / 65536
  have hXnat : 2 ^ 32 ≤ poolMaximum n := by
    have hh := le_of_lt (fw_poolMaximum_gt_four_seed lower hn)
    norm_num at hh ⊢
    exact hh
  have hX : (4294967296 : ℝ) ≤ X := by dsimp [X]; exact_mod_cast hXnat
  have hXp : 0 < X := by linarith
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Nat.mul_pos (by omega : 0 < n) (by omega : 0 < n)
  have hu : 0 < u := by dsimp [u]; linarith
  have hq : 0 < q := div_pos hN hXp
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hsqrt : Real.sqrt X ≤ X / 65536 := by
    have hprod : 0 ≤ X * (X - 4294967296) := mul_nonneg hXp.le (by linarith)
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have he : D * u / X ≤ c := by
    dsimp [D, c]
    apply (div_le_iff₀ hXp).2
    have h : (281649 / 62500 : ℝ) * (Real.sqrt X / u) * u =
        (281649 / 62500 : ℝ) * Real.sqrt X := by field_simp
    rw [h]
    nlinarith
  have hE : E ≤ D / N := by
    dsimp [E]
    have hcast : (((poolMaximum n - 2 : ℕ) : ℝ)) ≤ X := by
      dsimp [X]; exact_mod_cast Nat.sub_le (poolMaximum n) 2
    have hp := mul_le_mul_of_nonneg_right hcast hD
    apply (div_le_iff₀ (mul_pos hN hXp)).2
    have hid : D / N * (N * X) = X * D := by field_simp
    rw [hid]
    nlinarith
  have hLi : 0 ≤ liFromTwo 4 ∧ liFromTwo 4 ≤ 4 := by
    constructor
    · have hm := liFromTwo_mono (show (2 : ℝ) ≤ 2 by norm_num) (show (2 : ℝ) ≤ 4 by norm_num)
      simpa [liFromTwo] using hm
    · have hm := liFromTwo_le_two_mul (show (2 : ℝ) ≤ 4 by norm_num)
      linarith
  have hDN : D / N ≤ c / (u * q) := by
    have h := div_le_div_of_nonneg_right he (le_of_lt (mul_pos hu hq))
    have hid : (D * u / X) / (u * q) = D / N := by
      dsimp [q]
      field_simp
    rw [hid] at h
    exact h
  have hsqX : (4294967296 : ℝ)^2 ≤ X^2 := by nlinarith
  have hLiBound : liFromTwo 4 / (N * X) ≤
      4 * u / ((2 ^ 32 : ℝ)^2 * (u * q)) := by
    have hmain : liFromTwo 4 / (N * X) ≤ 4 / (N * X) :=
      div_le_div_of_nonneg_right hLi.2 (mul_pos hN hXp).le
    have hx : 4 / (N * X) ≤ 4 / (q * (4294967296 : ℝ)^2) := by
      apply (div_le_div_iff₀ (mul_pos hN hXp) (mul_pos hq (by positivity))).2
      dsimp [q]
      field_simp
      nlinarith
    have hid : 4 / (q * (4294967296 : ℝ)^2) =
        4 * u / ((2 ^ 32 : ℝ)^2 * (u * q)) := by norm_num; field_simp
    exact hmain.trans (hid ▸ hx)
  have hBG : bgLiUpperNorm u / N ≤
      (1 + 1/u + 4/u^2) / ((2 ^ 32 : ℝ) * (u * q)) := by
    have hB : 0 ≤ 1 + 1/u + 4/u^2 := by positivity
    have heq : bgLiUpperNorm u / N = (1 + 1/u + 4/u^2) / (X * (u*q)) := by
      dsimp [bgLiUpperNorm, q]
      field_simp
    rw [heq]
    apply div_le_div_of_nonneg_left hB (by positivity)
    exact mul_le_mul_of_nonneg_right (by norm_num; exact hX) (mul_pos hu hq).le
  have hsum : D / N + E ≤ 2 * c / (u * q) := by
    calc
      D / N + E ≤ c / (u * q) + c / (u * q) := add_le_add hDN (hE.trans hDN)
      _ = 2 * c / (u * q) := by ring
  exact ⟨he, hE, hLi, hsum, hLiBound, hBG⟩

end
end Sude
