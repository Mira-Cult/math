import Sude.FWSelectedCapacityCYChoiceGrid
import Sude.FWCanonicalCYFamilyChoiceGrids
import Sude.FWPermutedRadiusCapacity
import Sude.FWThetaInputs
import Sude.FWPoolBound
import Sude.FlowRealization

/-! Extend the exact selected capacity completion with canonical four-family
choice grids and their separate side capacities. Original completion facts
are retained. No post-centering margin or prime target is inferred. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- The same selected CY square has both physical choice grids, the canonical
signed gaps, and actual stage-permuted side-radius capacity. -/
theorem fw_selected_capacity_cy_family_grids
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta)
    (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    (n : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hodd : Odd n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card) :
    let w := fwSelectedCapacityThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hprime hcount
    let f := w.family
    let old := fw_selected_capacity_theta_frozen_cy_all_line_flows mv bmor upper lower sharp upperSharp n hnlo hnhi hodd otherChoice a seeds hseed hprime hcount
    let completion := old.2.2.2.2.2.2
    let cy := Classical.choose (Classical.choose_spec completion)
    let facts := Classical.choose_spec (Classical.choose_spec completion)
    let prior := fw_selected_capacity_cy_choice_grids mv bmor upper lower sharp upperSharp n hnlo hnhi hodd otherChoice a seeds hseed hprime hcount
    let choice := fwSelectedThetaChoice hnlo otherChoice
    let labels := fwActiveRectangleLabels n f.stages.length f.stageCap
    let gap := fwOrderedCanonicalRectangleGap f
    fwRetainedProposition prior ∧ fwRetainedProposition facts ∧
    (poolMaximum n : ℝ) / 23 ≤ f.last ∧
    (∀ z ∈ fwThetaFamilyFull f, entry cy z = entry w.oldReference z) ∧
    (∀ side, CompleteEvenGrid (labels.filter fun i => choice i = side) gap (fwCanonicalFamilyRadius f side) ∧
      2 ∣ fwCanonicalFamilyRadius f side ∧
      2 * ((n / 450) * poolMaximum n) ≤ fwCanonicalFamilyRadius f side ∧
      2 * (((n / 450) * poolMaximum n) / 2) ≤ evenGridCenter (fwCanonicalFamilyRadius f side)) ∧
    (∀ i ∈ labels,
      entry cy (packedRectangleCorner f.hs choice (i,1)) =
        entry cy (packedRectangleCorner f.hs choice (i,0)) + gap i ∧
      entry cy (packedRectangleCorner f.hs choice (i,2)) =
        entry cy (packedRectangleCorner f.hs choice (i,3)) + gap i) ∧
    (∀ out : Cell n ≃ Fin (n*n),
      (∀ z ∈ packedRectangleSupport f.hs choice, entry out z = entry cy z) →
      ∀ i ∈ labels,
        entry out (packedRectangleCorner f.hs choice (i,1)) =
          entry out (packedRectangleCorner f.hs choice (i,0)) + gap i ∧
        entry out (packedRectangleCorner f.hs choice (i,2)) =
          entry out (packedRectangleCorner f.hs choice (i,3)) + gap i) := by
  classical
  dsimp only
  let w := fwSelectedCapacityThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hprime hcount
  let old := fw_selected_capacity_theta_frozen_cy_all_line_flows mv bmor upper lower sharp upperSharp n hnlo hnhi hodd otherChoice a seeds hseed hprime hcount
  let completion := old.2.2.2.2.2.2
  let cy := Classical.choose (Classical.choose_spec completion)
  let facts := Classical.choose_spec (Classical.choose_spec completion)
  let prior := fw_selected_capacity_cy_choice_grids mv bmor upper lower sharp upperSharp n hnlo hnhi hodd otherChoice a seeds hseed hprime hcount
  have hlarge : (4 * 2^30 : ℝ) < poolMaximum n := by
    exact_mod_cast fw_poolMaximum_gt_four_seed lower hnlo
  have hX : (100 : ℝ) ≤ poolMaximum n := by norm_num at hlarge ⊢; linarith
  have hm := fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo (by omega : n ≤ 35733)
  have hgrids := fw_canonical_cy_family_choice_grids hnlo otherChoice w.family w.p w.oldReference
    w.roles w.network cy facts.2.2.1 w.cross hX hm.1 hm.2
  refine ⟨prior, facts, w.cross, facts.2.2.1, ?_, hgrids.2.2.1, hgrids.2.2.2⟩
  intro side
  have hwide := fw_permuted_wide_gap_total_lower
    ((Lucas.poolTotal n : ℝ) / (n*n : ℕ)) hX hm.1 hm.2
    w.family.blocks w.family.hlen w.family.hmatched w.family.πw (fwCanonicalFamilyDestination side)
  have hcapacity : 2 * ((n / 450) * poolMaximum n) ≤ fwCanonicalFamilyRadius w.family side := by
    dsimp [fwCanonicalFamilyRadius]
    omega
  exact ⟨(hgrids.1 side).1, (hgrids.1 side).2, hcapacity,
    evenGridCenter_pays_capacity _ _ hcapacity⟩

end
end Sude
