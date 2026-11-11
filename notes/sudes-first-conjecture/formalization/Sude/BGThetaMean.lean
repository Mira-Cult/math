import Sude.BGThetaMeanFromAggregate
import Sude.OddCountUniformTheta

/-! The BG mean lower bound from the explicit finite BMOR theta input.
No stronger classwise prime-count hypothesis is used. -/
namespace Sude
noncomputable section

/-- The normalized BG mean bound, derived from the finite theta estimate. -/
theorem bg_actual_pool_normalized_mean_lower_of_theta
    (bmor : BMORFiniteTheta) {n : ℕ} (hn : 0 < n)
    (hloglo : (24 : ℝ) ≤ Real.log (poolMaximum n : ℝ))
    (hloghi : Real.log (poolMaximum n : ℝ) ≤ 29)
    (hcap : (poolMaximum n : ℝ) ≤ (4 * 10 ^ 13 : ℝ)) :
    (487 / 1000 : ℝ) < ((Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ)) /
      (poolMaximum n : ℝ) := by
  have hcount := bmor_odd_count_uniform_bound_of_theta bmor
    (X := (poolMaximum n : ℝ)) (by linarith) hcap
  exact bg_actual_pool_normalized_mean_lower_of_aggregate hn hloglo hloghi hcount

/-- The same BG mean bound before normalization by the pool maximum. -/
theorem bg_actual_pool_mean_lower_of_theta
    (bmor : BMORFiniteTheta) {n : ℕ} (hn : 0 < n)
    (hloglo : (24 : ℝ) ≤ Real.log (poolMaximum n : ℝ))
    (hloghi : Real.log (poolMaximum n : ℝ) ≤ 29)
    (hcap : (poolMaximum n : ℝ) ≤ (4 * 10 ^ 13 : ℝ)) :
    (487 / 1000 : ℝ) * (poolMaximum n : ℝ) <
      (Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ) := by
  have hX : 0 < (poolMaximum n : ℝ) := by
    exact_mod_cast (poolMaximum_prime n).pos
  exact (lt_div_iff₀ hX).mp
    (bg_actual_pool_normalized_mean_lower_of_theta bmor hn hloglo hloghi hcap)

end
end Sude
