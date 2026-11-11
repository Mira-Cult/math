import Sude.StageHalfGapConcentration
import Sude.StageLineExplicitMean

/-! Exact cancellation of source-stage means for equal-size destination
families, using one common stage-permutation assignment. -/
namespace Sude
noncomputable section

/-- Equal slot cardinalities cancel the source-stage means. No disjointness,
physical geometry, probability event, or bound on the gaps is required. -/
theorem stage_half_gap_score_difference {W B : ℕ} (hB : 0 < B)
    (left right : Fin W → Finset (Fin B))
    (values : Fin W → Fin B → ℝ) (π : Fin W → Equiv.Perm (Fin B))
    (hcard : ∀ j, (left j).card = (right j).card) :
    stageHalfGapScore left values π - stageHalfGapScore right values π =
      (1/2 : ℝ) * ((∑ j, ∑ b ∈ left j, values j (π j b)) -
        ∑ j, ∑ b ∈ right j, values j (π j b)) := by
  classical
  have hlocal (j : Fin W) :
      stageWeightedCentered left (fun _ _ => (1/2 : ℝ)) values j (π j) -
          stageWeightedCentered right (fun _ _ => (1/2 : ℝ)) values j (π j) =
        (1/2 : ℝ) * ((∑ b ∈ left j, values j (π j b)) -
          ∑ b ∈ right j, values j (π j b)) := by
    rw [stageWeightedCentered_eq_explicit_mean hB,
      stageWeightedCentered_eq_explicit_mean hB]
    have hweights : (∑ b ∈ left j, (1/2 : ℝ)) = ∑ b ∈ right j, (1/2 : ℝ) := by
      simp only [Finset.sum_const, hcard j]
    rw [hweights]
    simp only [← Finset.mul_sum]
    ring
  unfold stageHalfGapScore
  calc
    _ = ∑ j, (stageWeightedCentered left (fun _ _ => (1/2 : ℝ)) values j (π j) -
        stageWeightedCentered right (fun _ _ => (1/2 : ℝ)) values j (π j)) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ j, (1/2 : ℝ) * ((∑ b ∈ left j, values j (π j b)) -
        ∑ b ∈ right j, values j (π j b)) := by simp_rw [hlocal]
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_sub_distrib]

end
end Sude
