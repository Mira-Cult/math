import Sude.LiIntegralBridge

/-! Propagation of the BG logarithmic-integral comparisons from explicit
base inequalities at 2048. The base inequalities are not established here. -/

namespace Sude
noncomputable section

/-- BG's lower comparison expression. -/
def bgLiLower (x : ℝ) : ℝ :=
  x / Real.log x + x / (Real.log x)^2 + 2*x / (Real.log x)^3 +
    6*x / (Real.log x)^4

/-- BG's upper comparison expression. -/
def bgLiUpper (x : ℝ) : ℝ :=
  x / Real.log x + x / (Real.log x)^2 + 4*x / (Real.log x)^3

private theorem log_2048_gt_six : (6 : ℝ) < Real.log 2048 := by
  have hpow : (2048 : ℝ) = 2 ^ (11 : ℕ) := by norm_num
  rw [hpow, Real.log_pow]
  have h := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

private theorem log_gt_six {x : ℝ} (hx : 2048 ≤ x) : 6 < Real.log x := by
  have h := Real.log_le_log (show (0 : ℝ) < 2048 by norm_num) hx
  linarith [log_2048_gt_six]

theorem bgLiUpper_gap_deriv {x : ℝ} (hx : 2 ≤ x) :
    HasDerivAt (fun t => bgLiUpper t - liFromTwo t)
      ((2 * Real.log x - 12) / (Real.log x)^4) x := by
  have hxpos : x ≠ 0 := by linarith
  have hl : Real.log x ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  have hdlog := Real.hasDerivAt_log hxpos
  have hdid := hasDerivAt_id x
  have hli := liFromTwo_hasDerivAt (show 2 ≤ x by linarith)
  have hraw := (((hdid.div hdlog hl).add
    (hdid.div (hdlog.pow 2) (pow_ne_zero 2 hl))).add
      (((hdid.const_mul 4).div (hdlog.pow 3) (pow_ne_zero 3 hl)))).sub hli
  have heq :
      (1 * Real.log x - x * x⁻¹) / (Real.log x)^2 +
      (1 * (Real.log x)^2 - x * (2 * (Real.log x)^1 * x⁻¹)) / ((Real.log x)^2)^2 +
      ((4 * 1) * (Real.log x)^3 - (4*x) * (3 * (Real.log x)^2 * x⁻¹)) / ((Real.log x)^3)^2 -
      (Real.log x)⁻¹ = (2 * Real.log x - 12) / (Real.log x)^4 := by
    field_simp
    ring
  convert hraw using 1 <;> try rfl
  symm
  simpa only [id_eq, one_mul, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one] using heq

theorem bgLiLower_gap_deriv {x : ℝ} (hx : 2 ≤ x) :
    HasDerivAt (fun t => liFromTwo t - bgLiLower t)
      (24 / (Real.log x)^5) x := by
  have hxpos : x ≠ 0 := by linarith
  have hl : Real.log x ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  have hdlog := Real.hasDerivAt_log hxpos
  have hdid := hasDerivAt_id x
  have hli := liFromTwo_hasDerivAt (show 2 ≤ x by linarith)
  have hraw := hli.sub ((((hdid.div hdlog hl).add
    (hdid.div (hdlog.pow 2) (pow_ne_zero 2 hl))).add
      ((hdid.const_mul 2).div (hdlog.pow 3) (pow_ne_zero 3 hl))).add
        ((hdid.const_mul 6).div (hdlog.pow 4) (pow_ne_zero 4 hl)))
  have heq : (Real.log x)⁻¹ -
      ((1 * Real.log x - x * x⁻¹) / (Real.log x)^2 +
      (1 * (Real.log x)^2 - x * (2 * (Real.log x)^1 * x⁻¹)) / ((Real.log x)^2)^2 +
      ((2 * 1) * (Real.log x)^3 - (2*x) * (3 * (Real.log x)^2 * x⁻¹)) / ((Real.log x)^3)^2 +
      ((6 * 1) * (Real.log x)^4 - (6*x) * (4 * (Real.log x)^3 * x⁻¹)) / ((Real.log x)^4)^2) =
        24 / (Real.log x)^5 := by
    field_simp
    ring
  convert hraw using 1 <;> try rfl
  symm
  simpa only [id_eq, one_mul, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one] using heq

/-- A strict upper comparison at 2048 propagates along the full ray. -/
theorem bg_li_upper_of_base
    (hbase : liFromTwo 2048 < bgLiUpper 2048) {x : ℝ} (hx : 2048 ≤ x) :
    liFromTwo x < bgLiUpper x := by
  have hm : MonotoneOn (fun t => bgLiUpper t - liFromTwo t) (Set.Ici 2048) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 2048)
    · intro t ht
      have ht' : 2048 ≤ t := ht
      exact (bgLiUpper_gap_deriv (by linarith : 2 ≤ t)).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : 2048 ≤ t := le_of_lt (by simpa using ht)
      exact (bgLiUpper_gap_deriv (by linarith : 2 ≤ t)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 2048 ≤ t := le_of_lt (by simpa using ht)
      rw [(bgLiUpper_gap_deriv (by linarith : 2 ≤ t)).deriv]
      apply div_nonneg
      · linarith [log_gt_six ht']
      · positivity
  have h := hm (show (2048 : ℝ) ∈ Set.Ici 2048 by simp) hx hx
  linarith

/-- A strict lower comparison at 2048 propagates along the full ray. -/
theorem bg_li_lower_of_base
    (hbase : bgLiLower 2048 < liFromTwo 2048) {x : ℝ} (hx : 2048 ≤ x) :
    bgLiLower x < liFromTwo x := by
  have hm : MonotoneOn (fun t => liFromTwo t - bgLiLower t) (Set.Ici 2048) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 2048)
    · intro t ht
      have ht' : 2048 ≤ t := ht
      exact (bgLiLower_gap_deriv (by linarith : 2 ≤ t)).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : 2048 ≤ t := le_of_lt (by simpa using ht)
      exact (bgLiLower_gap_deriv (by linarith : 2 ≤ t)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 2048 ≤ t := le_of_lt (by simpa using ht)
      rw [(bgLiLower_gap_deriv (by linarith : 2 ≤ t)).deriv]
      apply div_nonneg
      · norm_num
      · exact pow_nonneg (le_of_lt (by linarith [log_gt_six ht'])) _
  have h := hm (show (2048 : ℝ) ∈ Set.Ici 2048 by simp) hx hx
  linarith

end
end Sude
