import Sude.StageProbabilityBudget
import Sude.FiniteMomentSelection

/-! A positive conservative-invoice budget for the finite mixed selection
principle. No moment bound, physical slot identity or allocation is asserted. -/
namespace Sude
noncomputable section

/-- A common positive invoice and a uniform exponential moment bound pay
both signs of the finite logarithmic failure budget. -/
theorem mixed_moment_log_failure_budget {m : ℕ} (hm : 0 < m)
    (V : ℝ) (hV : 0 < V) (momentBound : Fin m → Bool → ℝ)
    (hbound : ∀ l b, momentBound l b ≤ Real.exp ((V / 4) *
      (4 * Real.sqrt (V * Real.log (4 * (m : ℝ)) / 2) / V) ^ 2 / 2)) :
    let threshold := Real.sqrt (V * Real.log (4 * (m : ℝ)) / 2)
    let t := 4 * threshold / V
    0 ≤ t ∧
      (∑ l, ∑ b, Real.exp (-t * threshold) * momentBound l b) ≤ 1 / 2 ∧
      (∑ l, ∑ b, Real.exp (-t * threshold) * momentBound l b) < 1 := by
  classical
  dsimp only
  let E := Real.sqrt (V * Real.log (4 * (m : ℝ)) / 2)
  let t := 4 * E / V
  let p : NNReal := ⟨V / 4, by positivity⟩
  have hp : (p : ℝ) = V / 4 := rfl
  have hp0 : p ≠ 0 := by
    intro h
    have hz : (p : ℝ) = 0 := by rw [h]; rfl
    rw [hp] at hz
    linarith
  have htail := zeroAwareTailBound_log_budget m hm V (le_of_lt hV) p (by rw [hp])
  change zeroAwareTailBound p E ≤ 1 / (2 * (m : ℝ)) at htail
  have hcalc : -t * E + (V / 4) * t ^ 2 / 2 = -E ^ 2 / (2 * (p : ℝ)) := by
    rw [hp]
    dsimp [t]
    field_simp
    ring
  have hsingle : Real.exp (-t * E) * Real.exp ((V / 4) * t ^ 2 / 2) ≤
      1 / (4 * (m : ℝ)) := by
    rw [zeroAwareTailBound, if_neg hp0] at htail
    rw [← Real.exp_add, hcalc]
    have heq : (1 : ℝ) / (2 * (m : ℝ)) = 2 * (1 / (4 * (m : ℝ))) := by ring
    rw [heq] at htail
    linarith
  have ht : 0 ≤ t := by dsimp [t, E]; positivity
  have hsum : (∑ l : Fin m, ∑ b : Bool,
      Real.exp (-t * E) * momentBound l b) ≤ 1 / 2 := by
    calc
      _ ≤ ∑ _l : Fin m, ∑ _b : Bool, (1 / (4 * (m : ℝ))) := by
        apply Finset.sum_le_sum
        intro l _
        apply Finset.sum_le_sum
        intro b _
        have hh := mul_le_mul_of_nonneg_left (hbound l b) (le_of_lt (Real.exp_pos (-t * E)))
        exact hh.trans hsingle
      _ = 1 / 2 := by
        have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
        simp
        field_simp
        norm_num
  exact ⟨ht, hsum, by linarith⟩

end
end Sude
