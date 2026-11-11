import Sude.StageHalfGapConcentration
import Sude.StageProbabilityBudget

/-! A positive-width logarithmic failure budget for the twelve-slot
stage-permutation score. No joint midpoint or physical selection is asserted. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory

local instance stageHalfGapBudgetPermMeasurable (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- Under a positive stage count and common positive gap width, this exact
logarithmic threshold has a two-sided failure probability at most 1/8. -/
theorem stage_half_gap_log_budget {W B : ℕ}
    (hW : 0 < W) (slots : Fin W → Finset (Fin B))
    (values : Fin W → Fin B → ℝ) (lo hi : Fin W → ℝ) (Δ : ℝ) (hΔ : 0 < Δ)
    (hwidth : ∀ j, hi j - lo j = Δ) (hcard : ∀ j, (slots j).card = 12)
    (hvalues : ∀ j b, values j b ∈ Set.Icc (lo j) (hi j)) :
    let E := Real.sqrt ((3/2 : ℝ) * W * Δ^2 * Real.log 16)
    (stagePermutationMeasure W B).real {π | E ≤ |stageHalfGapScore slots values π|} ≤ 1/8 := by
  dsimp only
  let v : ℝ := (3/4 : ℝ) * W * Δ^2
  have hWreal : 0 < (W : ℝ) := by exact_mod_cast hW
  have hv : 0 < v := by dsimp [v]; positivity
  let p : NNReal := ⟨v, le_of_lt hv⟩
  have hp : (p : ℝ) = v := rfl
  have hp0 : p ≠ 0 := by
    intro h
    have hz : (p : ℝ) = 0 := by rw [h]; rfl
    rw [hp] at hz
    linarith
  let E : ℝ := Real.sqrt ((3/2 : ℝ) * W * Δ^2 * Real.log 16)
  have hE : 0 ≤ E := Real.sqrt_nonneg _
  have htail := stage_half_gap_two_sided slots values lo hi Δ E (le_of_lt hΔ) hwidth hcard hvalues hE
  have hb := zeroAwareTailBound_log_budget 4 (by omega) (4*v) (by positivity) p (by rw [hp]; linarith)
  have harg : 4*v * Real.log (4 * (4 : ℝ)) / 2 =
      (3/2 : ℝ) * W * Δ^2 * Real.log 16 := by
    norm_num
    dsimp [v]
    ring
  have hsqrt : Real.sqrt (4*v * Real.log (4 * (4 : ℝ)) / 2) = E := by
    rw [harg]
  norm_num only [Nat.cast_ofNat] at hb hsqrt
  rw [hsqrt] at hb
  simp only [zeroAwareTailBound, if_neg hp0, hp] at hb
  change (stagePermutationMeasure W B).real {π | E ≤ |stageHalfGapScore slots values π|} ≤ 1/8
  exact htail.trans (by simpa only [v] using hb)

end
end Sude
