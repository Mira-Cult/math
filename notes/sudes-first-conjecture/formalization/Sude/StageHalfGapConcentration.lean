import Sude.PermutationStageMGF

/-! A finite stage-permutation estimate for half-weighted gaps on twelve
specified destination slots per stage. This does not assert physical slot
geometry, a joint midpoint event, or a selected-witness conclusion. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory

local instance stageHalfGapPermMeasurable (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- A half-weighted sum centered by each source stage's full mean. -/
def stageHalfGapScore {W B : ℕ} (slots : Fin W → Finset (Fin B))
    (values : Fin W → Fin B → ℝ) (π : Fin W → Equiv.Perm (Fin B)) : ℝ :=
  ∑ j, stageWeightedCentered slots (fun _ _ => (1/2 : ℝ)) values j (π j)

/-- Exactly twelve half-weighted slots give proxy `(3/4) * W * Δ²`.
The same fixed range width is used for every stage. -/
theorem stage_half_gap_proxy {W B : ℕ}
    (slots : Fin W → Finset (Fin B)) (lo hi : Fin W → ℝ) (Δ : ℝ)
    (hΔ : 0 ≤ Δ) (hwidth : ∀ j, hi j - lo j = Δ)
    (hcard : ∀ j, (slots j).card = 12) :
    ((stageWeightedProxy slots (fun _ _ => (1/2 : ℝ)) lo hi : NNReal) : ℝ) =
      (3/4 : ℝ) * W * Δ^2 := by
  have hle : ∀ j, lo j ≤ hi j := by
    intro j
    linarith [hwidth j]
  rw [stageWeightedProxy_real slots (fun _ _ => (1/2 : ℝ)) lo hi hle (by intro i j hj; norm_num)]
  calc
    _ = ∑ _j : Fin W, (Δ^2 / 4) * (12 * (1/2 : ℝ)^2) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hwidth j]
      simp only [Finset.sum_const, nsmul_eq_mul, hcard j, Nat.cast_ofNat]
    _ = (3/4 : ℝ) * W * Δ^2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The centered twelve-slot half-gap score has the stated two-sided tail.
No independence between this event and another event is asserted. -/
theorem stage_half_gap_two_sided {W B : ℕ}
    (slots : Fin W → Finset (Fin B)) (values : Fin W → Fin B → ℝ)
    (lo hi : Fin W → ℝ) (Δ ε : ℝ)
    (hΔ : 0 ≤ Δ) (hwidth : ∀ j, hi j - lo j = Δ)
    (hcard : ∀ j, (slots j).card = 12)
    (hvalues : ∀ j b, values j b ∈ Set.Icc (lo j) (hi j)) (hε : 0 ≤ ε) :
    (stagePermutationMeasure W B).real
      {π | ε ≤ |stageHalfGapScore slots values π|} ≤
      2 * Real.exp (-ε^2 / (2 * ((3/4 : ℝ) * W * Δ^2))) := by
  have h := stageWeighted_two_sided slots (fun _ _ => (1/2 : ℝ)) values lo hi ε
    (by intro i j hj; norm_num) hvalues hε
  simpa only [stageHalfGapScore, stage_half_gap_proxy slots lo hi Δ hΔ hwidth hcard] using h

end
end Sude
