import Sude.FWThetaInputs
namespace Sude
noncomputable section
set_option maxHeartbeats 800000

/-- The first-band frozen width and σ=11/100 satisfy separation and both endpoint margins. -/
theorem fw_first_band_frozen_cy_endpoints
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    let σ : ℝ := 11/100
    let ε : ℝ := 4262317/50000000
    let X : ℝ := poolMaximum n
    let m : ℝ := (Lucas.poolTotal n : ℝ) / (n*n : ℕ)
    σ+ε+3/(4*(n:ℝ)) < 1/4 ∧
    1 ≤ m-(σ+ε+3/(4*(n:ℝ)))*X ∧
    m+(σ+ε+3/(4*(n:ℝ)))*X ≤ X := by
  dsimp only
  have hn : (19485:ℝ) ≤ n := by exact_mod_cast hnlo
  have hnpos : (0:ℝ) < n := by linarith
  have hδ : 3/(4*(n:ℝ)) ≤ (1/100:ℝ) := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<4*(n:ℝ))).2
    nlinarith
  have hδpos : 0 ≤ 3/(4*(n:ℝ)) := by positivity
  have hXnat : 100 ≤ poolMaximum n := by
    have hp := fw_poolMaximum_gt_four_seed lower hnlo
    omega
  have hX : (100:ℝ) ≤ poolMaximum n := by exact_mod_cast hXnat
  obtain ⟨hlo,hhi⟩ := fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo (by omega)
  constructor
  · linarith
  constructor <;> nlinarith

end
end Sude
