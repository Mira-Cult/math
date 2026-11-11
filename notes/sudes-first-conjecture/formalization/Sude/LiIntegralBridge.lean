import Sude.BMORFinitePiFour
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Elementary regularity of the logarithmic integral on `[2,∞)`.
No analytic prime-count assumption is used. -/
open Set MeasureTheory
open scoped Interval

namespace Sude
noncomputable section

/-- The logarithmic-integral kernel is continuous on intervals above 1. -/
theorem li_kernel_continuousOn {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (fun t : ℝ => (Real.log t)⁻¹) (Set.Icc a b) := by
  have hlog : ContinuousOn Real.log (Set.Icc a b) := by
    apply Real.continuousOn_log.mono
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (by linarith [ht.1])
  apply hlog.inv₀
  intro t ht
  exact ne_of_gt (Real.log_pos (by linarith [ht.1]))

/-- The logarithmic-integral kernel is integrable on every ordered interval
with left endpoint greater than one. -/
theorem li_kernel_intervalIntegrable {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) MeasureTheory.volume a b :=
  (li_kernel_continuousOn ha).intervalIntegrable_of_Icc hab

/-- `liFromTwo` is monotone on `[2,∞)`. -/
theorem liFromTwo_mono {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    liFromTwo x ≤ liFromTwo y := by
  have h₁ := li_kernel_intervalIntegrable (a := 2) (b := x) (by norm_num) hx
  have h₂ := li_kernel_intervalIntegrable (a := x) (b := y) (by linarith) hxy
  have hsum := intervalIntegral.integral_add_adjacent_intervals h₁ h₂
  have hpos : 0 ≤ ∫ t in x..y, (Real.log t)⁻¹ := by
    apply intervalIntegral.integral_nonneg hxy
    intro t ht
    exact inv_nonneg.mpr (le_of_lt (Real.log_pos (by linarith [ht.1])))
  dsimp only [liFromTwo]
  linarith

/-- `liFromTwo` is continuous on every finite interval `[2,X]`. -/
theorem liFromTwo_continuousOn {X : ℝ} (hX : 2 ≤ X) :
    ContinuousOn liFromTwo (Set.Icc 2 X) := by
  have hi := li_kernel_intervalIntegrable (a := 2) (b := X) (by norm_num) hX
  have hc := intervalIntegral.continuousOn_primitive_interval' hi (by simp : (2 : ℝ) ∈ Set.uIcc 2 X)
  change ContinuousOn (fun x : ℝ => ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹) (Set.Icc 2 X)
  simpa only [Set.uIcc_of_le hX] using hc

private lemma li_integrand_cont (x : ℝ) (hx : 1 < x) :
    ContinuousAt (fun t : ℝ => (Real.log t)⁻¹) x := by
  exact (Real.continuousAt_log (by linarith)).inv₀ (ne_of_gt (Real.log_pos hx))

/-- The derivative of the integral normalized at 2 is `1 / log x`. -/
theorem liFromTwo_hasDerivAt {x : ℝ} (hx : 2 ≤ x) :
    HasDerivAt liFromTwo (Real.log x)⁻¹ x := by
  have hc : ContinuousOn (fun t : ℝ => (Real.log t)⁻¹) (Set.uIcc 2 x) := by
    rw [Set.uIcc_of_le hx]
    intro y hy
    exact (li_integrand_cont y (by linarith [hy.1])).continuousWithinAt
  have hm : StronglyMeasurableAtFilter (fun t : ℝ => (Real.log t)⁻¹) (nhds x) volume :=
    ContinuousAt.stronglyMeasurableAtFilter (isOpen_Ioi : IsOpen (Ioi (1 : ℝ)))
      (fun y hy => li_integrand_cont y hy) x (by change 1 < x; linarith)
  exact intervalIntegral.integral_hasDerivAt_right hc.intervalIntegrable hm
    (li_integrand_cont x (by linarith))

/-- Exact integral identity for the integral normalized at 2, valid for all
real `X ≥ 2`; it uses no prime-count estimates at `X²`. -/
theorem liFromTwo_integral_identity {X : ℝ} (hX : 2 ≤ X) :
    (∫ t in (2 : ℝ)..X, liFromTwo t) =
      X * liFromTwo X - liFromTwo (X ^ 2) + liFromTwo 4 := by
  have hc : ContinuousOn liFromTwo (Set.uIcc 2 X) := by
    rw [Set.uIcc_of_le hX]
    intro t ht
    exact (liFromTwo_hasDerivAt ht.1).continuousAt.continuousWithinAt
  have hd : ∀ t ∈ Set.uIcc 2 X,
      HasDerivAt (fun x => x * liFromTwo x - liFromTwo (x ^ 2)) (liFromTwo t) t := by
    rw [Set.uIcc_of_le hX]
    intro t ht
    have ht2 : 2 ≤ t ^ 2 := by nlinarith [ht.1]
    have hn : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    have h1 := (hasDerivAt_id t).fun_mul (liFromTwo_hasDerivAt ht.1)
    have hs : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
      simpa [pow_two, two_mul] using (hasDerivAt_id t).fun_mul (hasDerivAt_id t)
    have h2 := HasDerivAt.comp (h := fun x : ℝ => x ^ 2) t (liFromTwo_hasDerivAt ht2) hs
    have h2' : HasDerivAt (fun x => liFromTwo (x ^ 2))
        ((Real.log (t ^ 2))⁻¹ * (2 * t)) t := by
      simpa only [Function.comp_def] using h2
    have hderivEq : 1 * liFromTwo t + id t * (Real.log t)⁻¹ -
        (Real.log (t ^ 2))⁻¹ * (2 * t) = liFromTwo t := by
      simp only [Real.log_pow, Nat.cast_ofNat, id_eq, one_mul]
      field_simp
      ring
    have hh := h1.sub h2'
    rw [hderivEq] at hh
    exact hh

  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  have hzero : liFromTwo 2 = 0 := by simp [liFromTwo]
  simp only [hzero, mul_zero, zero_sub, sub_neg_eq_add] at h
  norm_num at h
  exact h


end
end Sude
