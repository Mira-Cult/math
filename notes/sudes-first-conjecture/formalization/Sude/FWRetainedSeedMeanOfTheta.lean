import Sude.FWRetainedSeedMeanPoolBound
import Sude.FWThetaInputs
import Sude.FWPoolBound
import Sude.ReservedPoolMean

/-! Retained twin mean bounds from the explicit finite-theta and RS inputs.
Seed eligibility and the endpoint cap remain supplied. -/
namespace Sude
noncomputable section

theorem fw_retained_seed_midpoint_pool_bound_of_theta
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n r P Q : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (seeds candidates : Finset ℕ) (hcandidates : candidates ⊆ seeds)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2^30)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P)
    (j : Fin P) (i : Fin Q) :
    |retainedStageMidpoint candidates r P Q 2 hcard kept hsub hkept j i -
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤
      (123 / 250 : ℝ) * (poolMaximum n : ℝ) := by
  rw [prescribedPoolValues_mean]
  have hX : 4 * (2^30 : ℝ) < (poolMaximum n : ℝ) := by
    exact_mod_cast fw_poolMaximum_gt_four_seed lower hnlo
  obtain ⟨hlo, hhi⟩ := fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo hnhi
  apply retained_seed_midpoint_pool_bound candidates r P Q hcard kept hsub hkept _ _ hX hlo hhi
  · intro j i
    exact hseed _ (hcandidates (sortedSeedLower_mem candidates r Q hcard _))

theorem fw_retained_seed_stage_mean_pool_bound_of_theta
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n r P Q : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (seeds candidates : Finset ℕ) (hcandidates : candidates ⊆ seeds)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2^30)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (hQ : 0 < Q)
    (j : Fin P) :
    |(∑ i : Fin Q, retainedStageMidpoint candidates r P Q 2 hcard kept hsub hkept j i) /
      (Q : ℝ) - centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤
      (123 / 250 : ℝ) * (poolMaximum n : ℝ) := by
  rw [prescribedPoolValues_mean]
  have hX : 4 * (2^30 : ℝ) < (poolMaximum n : ℝ) := by
    exact_mod_cast fw_poolMaximum_gt_four_seed lower hnlo
  obtain ⟨hlo, hhi⟩ := fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo hnhi
  apply retained_seed_stage_mean_pool_bound candidates r P Q hcard kept hsub hkept hQ _ _ hX hlo hhi
  · intro j i
    exact hseed _ (hcandidates (sortedSeedLower_mem candidates r Q hcard _))
end
end Sude
