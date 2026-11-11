import Sude.FWWheelFirstBandPointwise

/-! Exact first-band WW5 floor feasibility from a supplied even-gap trace.
This does not construct a trace or the frozen mixed growth recipe. -/
namespace Sude
noncomputable section

/-- The conservative first-band stock envelope stays positive and makes the
WW5 floor input nonnegative for every `j < 238` and every radius at least
`32 + 2j`. No numerical sampling or floor positivity assumption is used. -/
theorem fw_first_band_floor_of_radius {j R : ℕ} (hj : j < 238)
    (hR : 32 + 2 * j ≤ R) :
    let m : ℝ := 403 / 10000 - 2 * (1 / 69780 : ℝ) * j
    0 < m ∧ 0 ≤ (3981035 / 10000000 : ℝ) * m * R - 1 / 2 := by
  dsimp only
  let m : ℝ := 403 / 10000 - 2 * (1 / 69780 : ℝ) * j
  have hjR : (j : ℝ) ≤ 237 := by exact_mod_cast (show j ≤ 237 by omega)
  have hm : (33 / 1000 : ℝ) ≤ m := by dsimp [m]; linarith
  refine ⟨by linarith, ?_⟩
  by_cases hsmall : j ≤ 3
  · have hj' : (j : ℝ) ≤ 3 := by exact_mod_cast hsmall
    have hm' : (1 / 25 : ℝ) ≤ m := by dsimp [m]; linarith
    have hR' : (32 : ℝ) ≤ R := by exact_mod_cast (show 32 ≤ R by omega)
    have hp := mul_le_mul hm' hR' (by norm_num : (0 : ℝ) ≤ 32) (by positivity : 0 ≤ m)
    nlinarith
  · have hR' : (40 : ℝ) ≤ R := by exact_mod_cast (show 40 ≤ R by omega)
    have hp := mul_le_mul hm hR' (by norm_num : (0 : ℝ) ≤ 40) (by positivity : 0 ≤ m)
    nlinarith

/-- Every supplied growing trace from radius 32 adds a positive even gap at
each stage, so its actual final radius is at least `32 + 2*length` and even. -/
theorem fw_even_trace_radius_lower {Q : ℕ} {initial final : Finset ℕ}
    {last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 Q initial 32 final last stages) :
    32 + 2 * stages.length ≤ last ∧ 2 ∣ last := by
  have heach : ∀ stage ∈ stages, 2 ≤ stage.gap := by
    intro stage hs
    have h := trace.stage_properties stage hs
    exact Nat.le_of_dvd h.1 h.2.1
  have hsum : 2 * stages.length ≤ (stages.map BTSelectedStage.gap).sum := by
    have h := List.sum_le_sum (l := stages) (f := fun _ : BTSelectedStage => 2)
      (g := BTSelectedStage.gap) heach
    simpa [Nat.mul_comm] using h
  have hevenSum : 2 ∣ (stages.map BTSelectedStage.gap).sum := by
    apply List.dvd_sum
    intro x hx
    obtain ⟨stage, hs, rfl⟩ := List.mem_map.mp hx
    exact (trace.stage_properties stage hs).2.1
  have hlast := trace.final_accounting.2.2
  constructor
  · omega
  · rw [hlast]
    exact dvd_add (by decide) hevenSum

/-- A supplied even-gap trace beginning at the sixteen-seed radius automatically
satisfies the first-band WW5 floor condition at its actual final radius. -/
theorem fw_first_band_floor_of_even_trace {Q : ℕ} {initial final : Finset ℕ}
    {last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 Q initial 32 final last stages)
    (hj : stages.length < 238) :
    let m : ℝ := 403 / 10000 - 2 * (1 / 69780 : ℝ) * stages.length
    0 < m ∧ 0 ≤ (3981035 / 10000000 : ℝ) * m * last - 1 / 2 := by
  exact fw_first_band_floor_of_radius hj (fw_even_trace_radius_lower trace).1

end
end Sude
