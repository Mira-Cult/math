import Sude.PermutationStageMGF

/-! Expose the actual finite-stage means in the probability variables. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- A stage's centered weighted-permutation variable is the actual weighted
sum minus total slot weight times the mean of the complete stage values. -/
theorem stageWeightedCentered_eq_explicit_mean {P Q : ℕ} (hQ : 0 < Q)
    (slots : Fin P → Finset (Fin Q)) (weights values : Fin P → Fin Q → ℝ)
    (j : Fin P) (ω : Equiv.Perm (Fin Q)) :
    stageWeightedCentered slots weights values j ω =
      (∑ q ∈ slots j, weights j q * values j (ω q)) -
      (∑ q ∈ slots j, weights j q) * ((∑ q : Fin Q, values j q) / (Q : ℝ)) := by
  have hmean :
      (permutationHistoryMeasure ∅ (Equiv.refl (Fin Q)))[permutationWeightedSum (slots j) (weights j) (values j)] =
      (∑ q ∈ slots j, weights j q) * ((∑ q : Fin Q, values j q) / (Q : ℝ)) := by
    simpa [permutationWeightedSum] using
      permutationHistory_weighted_mean ∅ (slots j) (Equiv.refl (Fin Q)) ⟨0, hQ⟩
        (by simp) (by simp) (weights j) (values j)
  unfold stageWeightedCentered permutationWeightedCentered
  rw [hmean]
  rfl

/-- The labelled all-stage centered variable uses the actual separate mean
of each stage, with no independence assumption within a stage. -/
theorem stageLineCentered_eq_explicit_mean {m P Q : ℕ} (hQ : 0 < Q)
    (slots : Fin m → Fin P → Finset (Fin Q)) (weights : Fin m → Fin P → Fin Q → ℝ)
    (values : Fin P → Fin Q → ℝ) (l : Fin m) (ω : Fin P → Equiv.Perm (Fin Q)) :
    stageLineCentered slots weights values l ω =
      ∑ j, ((∑ q ∈ slots l j, weights l j q * values j (ω j q)) -
        (∑ q ∈ slots l j, weights l j q) * ((∑ q : Fin Q, values j q) / (Q : ℝ))) := by
  unfold stageLineCentered
  apply Finset.sum_congr rfl
  intro j _
  exact stageWeightedCentered_eq_explicit_mean hQ (slots l) (weights l) values j (ω j)

end
end Sude
