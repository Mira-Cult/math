import Sude.RegularFactorExceptions

/-! Charge central exceptional entries and the resulting exact mean shift. -/
namespace Sude
noncomputable section

/-- Deleting at most `t*n` entries within `radius` of the original mean
moves the remaining `k*n`-entry mean by at most `t*radius/k`.
The statement retains the scaled form used by every factor row and column. -/
theorem central_exception_mean_shift {α : Type*} [DecidableEq α]
    (unused chosen : Finset α) (value : α → ℝ) (k n t : ℕ) (radius : ℝ)
    (hsub : chosen ⊆ unused) (hk : 0 < k) (hn : 0 < n) (hrad : 0 ≤ radius)
    (hrest : (unused \ chosen).card = k * n) (hbudget : chosen.card ≤ t * n)
    (hnear : ∀ x ∈ chosen, |value x - centralEntriesMean unused value| ≤ radius) :
    |(k : ℝ) * (centralEntriesMean (unused \ chosen) value - centralEntriesMean unused value)| ≤
      (t : ℝ) * radius := by
  classical
  let μ := centralEntriesMean unused value
  let D := (∑ x ∈ chosen, value x) - (chosen.card : ℝ) * μ
  have hD : |D| ≤ (chosen.card : ℝ) * radius := by
    have hsum : |∑ x ∈ chosen, (value x - μ)| ≤ ∑ x ∈ chosen, |value x - μ| :=
      Finset.abs_sum_le_sum_abs _ _
    have hterm : (∑ x ∈ chosen, |value x - μ|) ≤ ∑ _x ∈ chosen, radius := by
      apply Finset.sum_le_sum
      intro x hx
      exact hnear x hx
    have heq : (∑ x ∈ chosen, (value x - μ)) = D := by
      simp [D, Finset.sum_sub_distrib]
    rw [heq] at hsum
    simpa using hsum.trans hterm
  have hpos : 0 < (unused \ chosen).card := by rw [hrest]; exact Nat.mul_pos hk hn
  have hupdate := central_entries_actual_mean_update unused chosen value hsub hpos
  have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have heq : (k : ℝ) * (centralEntriesMean (unused \ chosen) value - μ) = -D / (n : ℝ) := by
    rw [hupdate, hrest]
    push_cast
    dsimp [D, μ]
    field_simp
    ring
  rw [heq, abs_div, abs_neg, abs_of_pos hnreal]
  apply (div_le_iff₀ hnreal).2
  have hb : (chosen.card : ℝ) ≤ (t : ℝ) * n := by exact_mod_cast hbudget
  have hm := mul_le_mul_of_nonneg_right hb hrad
  nlinarith [hD]

/-- Add the exceptional-line error and the remaining-mean correction to the
strict sorted-block error, preserving strictness. -/
theorem central_exception_line_error (factorSum exceptionSum μ μf k m X t radius : ℝ)
    (hf : |factorSum - k * μf| < X)
    (he : |exceptionSum - m * μ| ≤ t * radius)
    (hm : |k * (μf - μ)| ≤ t * radius) :
    |factorSum + exceptionSum - (k + m) * μ| < X + 2 * t * radius := by
  have htriangle := abs_add_le (factorSum - k * μf) (exceptionSum - m * μ + k * (μf - μ))
  have htriangle₂ := abs_add_le (exceptionSum - m * μ) (k * (μf - μ))
  have hid : factorSum + exceptionSum - (k + m) * μ =
      (factorSum - k * μf) + (exceptionSum - m * μ + k * (μf - μ)) := by ring
  rw [hid]
  linarith

end
end Sude
