import Sude.FWThetaInputs
import Sude.ReservedPoolMean

/-! A first-band scalar ceiling for the proposed T75 window. It does not
construct target primes or establish any endpoint-window hypothesis. -/
namespace Sude
noncomputable section

/-- The window `n * μ / 1240`, centered at the actual pool mean `μ`, is
strictly smaller than `10X` on the first band, where `X` is the maximum of
the actual pool. -/
theorem fw_first_band_target_spread_lt_ten
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) :
    (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240 <
      10 * (poolMaximum n : ℝ) := by
  rw [prescribedPoolValues_mean]
  have hmean := (fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo (by omega)).2
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hn : (n : ℝ) ≤ 21248 := by exact_mod_cast hnhi
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hm := mul_le_mul_of_nonneg_left hmean hn0
  have hnx := mul_le_mul_of_nonneg_right hn hX.le
  nlinarith

end
end Sude
