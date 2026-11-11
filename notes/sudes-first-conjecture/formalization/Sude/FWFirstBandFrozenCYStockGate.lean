import Sude.FWThetaInputs
namespace Sude
noncomputable section
set_option maxHeartbeats 800000

/-- The frozen first-band completion width satisfies the CY stock gate.
The full value cover, unused-mean bound and final line budget are separate. -/
theorem fw_first_band_frozen_cy_stock_gate
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    ((3*n+1 : ℕ) : ℝ) ≤
      (2*((4262317/50000000 : ℝ)*poolMaximum n)-(1036/125 : ℝ)*Real.sqrt (poolMaximum n))/Real.log (poolMaximum n) -
        (((12*(n+8)*5+12*(n+8)*254+(2*n-1) : ℕ)) : ℝ) := by
  let X : ℝ := poolMaximum n
  let U : ℝ := Real.log X
  let N : ℝ := n
  have hn : (19485:ℝ) ≤ N := by dsimp [N]; exact_mod_cast hnlo
  have hU : (181/8:ℝ) < U := by simpa [U,X] using fw_poolMaximum_log_gt_181_eighths lower hnlo
  have hu : 0 < U := by linarith
  have hpos : 0 < N := by linarith
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hratio : U - 9/8 < X/N^2 := by
    simpa [U,X,N] using fw_actual_index_ratio_of_theta bmor lower upper hnlo (by omega)
  have hratio' : (U - 9/8)*N^2 < X := (lt_div_iff₀ (sq_pos_of_pos hpos)).mp hratio
  have hcoeff : (19/20 : ℝ)*U ≤ U - 9/8 := by linarith
  have hm := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg N)
  have hxdiv : (19/20 : ℝ)*N^2 ≤ X/U := by
    apply (le_div_iff₀ hu).2
    nlinarith
  have hnat := poolMaximum_below_two_pow_41 upper n (by omega) (by omega)
  have hxcap : X < (2:ℝ)^41 := by dsimp [X]; exact_mod_cast hnat
  have hsqrt : Real.sqrt X ≤ 2^21 := by
    have hs := Real.sq_sqrt (le_of_lt hX)
    have hsp := Real.sqrt_nonneg X
    norm_num at hxcap ⊢
    nlinarith
  have hsqrtdiv : Real.sqrt X / U ≤ 95000 := by
    apply (div_le_iff₀ hu).2
    nlinarith
  have hminsq : (19485 : ℝ)*N ≤ N^2 := by nlinarith
  have hnsub : 1 ≤ 2*n := by omega
  have hcast : (((12*(n+8)*5+12*(n+8)*254+(2*n-1) : ℕ)) : ℝ) = 3110*N + 24863 := by
    rw [Nat.cast_add, Nat.cast_sub hnsub]
    dsimp [N]
    push_cast
    ring
  have hcost : ((3*n+1 : ℕ) : ℝ) + (((12*(n+8)*5+12*(n+8)*254+(2*n-1) : ℕ)) : ℝ) ≤
      (80984023/500000000 : ℝ)*N^2 - (1036/125 : ℝ)*95000 := by
    rw [hcast]
    dsimp [N] at *
    push_cast
    nlinarith
  have hbound : (80984023/500000000 : ℝ)*N^2 - (1036/125 : ℝ)*95000 ≤
      (2*((4262317/50000000 : ℝ)*X)-(1036/125 : ℝ)*Real.sqrt X)/U := by
    have hid : (2*((4262317/50000000 : ℝ)*X)-(1036/125 : ℝ)*Real.sqrt X)/U =
        (4262317/25000000 : ℝ)*(X/U) - (1036/125 : ℝ)*(Real.sqrt X/U) := by ring
    rw [hid]
    linarith
  change ((3*n+1 : ℕ) : ℝ) ≤
      (2*((4262317/50000000 : ℝ)*X)-(1036/125 : ℝ)*Real.sqrt X)/U -
        (((12*(n+8)*5+12*(n+8)*254+(2*n-1) : ℕ)) : ℝ)
  linarith

end
end Sude
