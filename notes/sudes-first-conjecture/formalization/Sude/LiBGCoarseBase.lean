import Sude.LiBGPropagation

/-! Coarse unconditional base bounds and monotonicity for the BG gaps. -/
namespace Sude
noncomputable section

/-- The lower gap is increasing on the entire nonsingular domain [2,∞). -/
theorem bg_lower_gap_monotone :
    MonotoneOn (fun x => liFromTwo x - bgLiLower x) (Set.Ici 2) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 2)
  · intro x hx
    exact (bgLiLower_gap_deriv hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 2 ≤ x := le_of_lt (by simpa using hx)
    exact (bgLiLower_gap_deriv hx').differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 2 ≤ x := le_of_lt (by simpa using hx)
    rw [(bgLiLower_gap_deriv hx').deriv]
    have hl : 0 < Real.log x := Real.log_pos (by linarith)
    positivity

/-- The upper gap is increasing from exp(6) onward. -/
theorem bg_upper_gap_monotone :
    MonotoneOn (fun x => bgLiUpper x - liFromTwo x) (Set.Ici (Real.exp 6)) := by
  have he : (2 : ℝ) ≤ Real.exp 6 := by linarith [Real.add_one_le_exp (6 : ℝ)]
  apply monotoneOn_of_deriv_nonneg (convex_Ici (Real.exp 6))
  · intro x hx
    exact (bgLiUpper_gap_deriv (he.trans hx)).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : Real.exp 6 ≤ x := le_of_lt (by simpa using hx)
    exact (bgLiUpper_gap_deriv (he.trans hx')).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : Real.exp 6 ≤ x := le_of_lt (by simpa using hx)
    have hlog : (6 : ℝ) ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 6) hx'
      simpa using h
    rw [(bgLiUpper_gap_deriv (he.trans hx')).deriv]
    apply div_nonneg
    · linarith
    · positivity

/-- At two, the lower gap has a certified coarse rational lower bound. -/
theorem bg_lower_gap_at_two_gt :
    (-82 : ℝ) < liFromTwo 2 - bgLiLower 2 := by
  have hz : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hzi : (Real.log 2)⁻¹ ≤ (3 / 2 : ℝ) := by
    have h := one_div_le_one_div_of_le (show (0 : ℝ) < 2 / 3 by norm_num) hz
    norm_num at h
    exact h
  have hzi0 : 0 ≤ (Real.log 2)⁻¹ := by positivity
  have h2 := pow_le_pow_left₀ hzi0 hzi 2
  have h3 := pow_le_pow_left₀ hzi0 hzi 3
  have h4 := pow_le_pow_left₀ hzi0 hzi 4
  have heq : bgLiLower 2 = 2 * (Real.log 2)⁻¹ + 2 * ((Real.log 2)⁻¹)^2 +
      4 * ((Real.log 2)⁻¹)^3 + 12 * ((Real.log 2)⁻¹)^4 := by
    unfold bgLiLower
    simp only [div_eq_mul_inv, inv_pow]
    ring
  have hli : liFromTwo 2 = 0 := by simp [liFromTwo]
  rw [hli, heq]
  norm_num at h2 h3 h4 ⊢
  linarith

/-- A linear bound for the logarithmic integral on the positive source domain. -/
theorem liFromTwo_le_two_mul {x : ℝ} (hx : 2 ≤ x) : liFromTwo x ≤ 2*x-4 := by
  have hm : MonotoneOn (fun t : ℝ => 2*t - liFromTwo t) (Set.Ici 2) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 2)
    · intro t ht
      exact (((hasDerivAt_id t).const_mul 2).sub (liFromTwo_hasDerivAt ht)).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : 2 ≤ t := le_of_lt (by simpa using ht)
      exact (((hasDerivAt_id t).const_mul 2).sub (liFromTwo_hasDerivAt ht')).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 2 ≤ t := le_of_lt (by simpa using ht)
      have hl : (1 / 2 : ℝ) ≤ Real.log t := by
        have h := Real.log_le_log (show (0 : ℝ) < 2 by norm_num) ht'
        linarith [Real.log_two_gt_d9]
      have hi : (Real.log t)⁻¹ ≤ 2 := by
        have h := one_div_le_one_div_of_le (show (0 : ℝ) < 1 / 2 by norm_num) hl
        norm_num at h
        exact h
      have hd := (((hasDerivAt_id t).const_mul 2).sub (liFromTwo_hasDerivAt ht'))
      change 0 ≤ deriv ((fun y : ℝ => 2 * id y) - liFromTwo) t
      rw [hd.deriv]
      linarith
  have h := hm (show (2 : ℝ) ∈ Set.Ici 2 by simp) hx hx
  have hli : liFromTwo 2 = 0 := by simp [liFromTwo]
  dsimp only at h
  linarith

/-- At exp(6), the upper gap has a certified coarse rational lower bound. -/
theorem bg_upper_gap_at_exp_six_gt :
    (-1458 : ℝ) < bgLiUpper (Real.exp 6) - liFromTwo (Real.exp 6) := by
  have he2 : (2 : ℝ) ≤ Real.exp 6 := by linarith [Real.add_one_le_exp (6 : ℝ)]
  have hexp : Real.exp 6 ≤ (729 : ℝ) := by
    have h := Real.exp_one_lt_d9
    have hp : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
    have hpow : Real.exp 1 ^ 6 ≤ (3 : ℝ)^6 := pow_le_pow_left₀ hp.le (by linarith) 6
    have hid : Real.exp 1 ^ 6 = Real.exp 6 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [hid] at hpow
    norm_num at hpow
    exact hpow
  have hU : 0 ≤ bgLiUpper (Real.exp 6) := by
    unfold bgLiUpper
    rw [Real.log_exp]
    positivity
  have hli := liFromTwo_le_two_mul he2
  linarith

end
end Sude
