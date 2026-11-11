import Sude.BMORFinitePiFour
import Mathlib.NumberTheory.Chebyshev

/-! An exact real-endpoint Abel identity for odd-prime counting. -/

namespace Sude
noncomputable section
open Finset Real MeasureTheory

/-- The q=2 theta prefix is the logarithmic sum over odd primes, with the
same closed real endpoint used by `oddPrimeCountReal`. -/
theorem thetaAP_two_eq_sum_oddPrimePrefix (x : ℝ) :
    thetaAP x 2 1 = ∑ p ∈ oddPrimePrefix ⌊x⌋₊, Real.log p := by
  rw [thetaAP_eq_sum_apPrefix]
  congr 1
  ext p
  simp only [apPrefix, oddPrimePrefix, mem_filter, mem_range]
  constructor
  · rintro ⟨hp, hprime, hmod⟩
    refine ⟨hp, hprime, ?_⟩
    intro h
    subst p
    norm_num at hmod
  · rintro ⟨hp, hprime, hne⟩
    refine ⟨hp, hprime, ?_⟩
    have hodd := hprime.eq_two_or_odd.resolve_left hne
    have hmod : p % 2 = 1 := by omega
    exact_mod_cast hmod

set_option backward.isDefEq.respectTransparency.types false in
/-- Abel summation for the actual odd-prime prefix, including both the
closed upper endpoint and the empty prefix at 2. -/
theorem oddPrimeCountReal_eq_theta_div_log_add_integral {x : ℝ} (hx : 2 ≤ x) :
    oddPrimeCountReal x = thetaAP x 2 1 / log x +
      ∫ t in (2 : ℝ)..x, thetaAP t 2 1 / (t * log t ^ 2) := by
  let a : ℕ → ℝ := Set.indicator {n | Nat.Prime n ∧ n ≠ 2} (fun n ↦ log n)
  have ha (y : ℝ) : ∑ n ∈ Icc 0 ⌊y⌋₊, a n = thetaAP y 2 1 := by
    rw [thetaAP_two_eq_sum_oddPrimePrefix]
    simp [a, Set.indicator_apply, oddPrimePrefix, _root_.Nat.range_succ_eq_Icc_zero, sum_filter]
  have hc : oddPrimeCountReal x = ∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * a n := by
    unfold oddPrimeCountReal oddPrimePrefix
    rw [card_eq_sum_ones, _root_.Nat.range_succ_eq_Icc_zero, sum_filter]
    push_cast
    refine sum_congr rfl fun n hn ↦ ?_
    split_ifs with h
    · have hp := h.1
      have hlog : log n ≠ 0 := log_ne_zero_of_pos_of_ne_one (mod_cast hp.pos) (mod_cast hp.ne_one)
      simp [a, h, hlog]
    · simp [a, h]
  rw [hc, sum_mul_eq_sub_integral_mul₁ a (f := fun n ↦ (log n)⁻¹)
    (by simp [a]) (by simp [a]), ← intervalIntegral.integral_of_le hx]
  · have int_deriv (f : ℝ → ℝ) :
        ∫ u in 2..x, deriv (fun x ↦ (log x)⁻¹) u * f u =
        ∫ u in 2..x, f u * -(u * log u ^ 2)⁻¹ :=
      intervalIntegral.integral_congr fun u _ ↦ by simp [field]
    rw [int_deriv]
    simp only [ha]
    simp [div_eq_mul_inv, mul_comm]
  · intro z ⟨_, _⟩
    have : z ≠ 0 := by linarith
    have : log z ≠ 0 := by apply log_ne_zero_of_pos_of_ne_one <;> linarith
    fun_prop
  · refine ContinuousOn.integrableOn_Icc fun z ⟨_, _⟩ ↦ ContinuousWithinAt.congr ?_
      (fun _ _ ↦ deriv_inv_log_apply) deriv_inv_log_apply
    have : z ≠ 0 := by linarith
    have : log z ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 <| log_ne_zero_of_pos_of_ne_one ?_ ?_ <;> linarith
    exact ContinuousAt.continuousWithinAt <| by fun_prop

end
end Sude
