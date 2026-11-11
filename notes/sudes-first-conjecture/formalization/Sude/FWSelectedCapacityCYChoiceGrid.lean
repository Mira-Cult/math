import Sude.FWSelectedCapacityFrozenCYAllLineFlows
import Sude.FWCanonicalCYSeedGrowthGrid

/-! Extend the exact selected capacity completion with its physical choice grids.
The selected completion's complete original proposition is retained on the
same chosen diagonal and CY squares. No post-centering or prime claim is made. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

/-- Expose the proposition proved by a supplied proof, without restating it. -/
def fwRetainedProposition {P : Prop} (_ : P) : Prop := P

/-- The completion selected by the original capacity theorem retains every
original field, while both physical choice grids hold through the same trace
radius. The crossing bound is the selected witness's original bound. -/
theorem fw_selected_capacity_cy_choice_grids
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
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
    let diag := Classical.choose completion
    let cy := Classical.choose (Classical.choose_spec completion)
    let facts := Classical.choose_spec (Classical.choose_spec completion)
    let labels := fwActiveRectangleLabels n f.stages.length f.stageCap
    let gap := fwOrderedCanonicalRectangleGap f
    fwRetainedProposition old ∧ fwRetainedProposition facts ∧
    (poolMaximum n : ℝ) / 23 ≤ f.last ∧
    (∀ z ∈ fwThetaFamilyFull f, entry cy z = entry w.oldReference z) ∧
    CompleteEvenGrid (labels.filter fun i => fwSelectedThetaChoice hnlo otherChoice i = true) gap f.last ∧
    CompleteEvenGrid (labels.filter fun i => fwSelectedThetaChoice hnlo otherChoice i = false) gap f.last ∧
    2 ∣ f.last ∧
    (∀ i ∈ labels,
      entry cy (packedRectangleCorner f.hs (fwSelectedThetaChoice hnlo otherChoice) (i,1)) =
        entry cy (packedRectangleCorner f.hs (fwSelectedThetaChoice hnlo otherChoice) (i,0)) + gap i ∧
      entry cy (packedRectangleCorner f.hs (fwSelectedThetaChoice hnlo otherChoice) (i,2)) =
        entry cy (packedRectangleCorner f.hs (fwSelectedThetaChoice hnlo otherChoice) (i,3)) + gap i) := by
  classical
  dsimp only
  let w := fwSelectedCapacityThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hprime hcount
  let old := fw_selected_capacity_theta_frozen_cy_all_line_flows mv bmor upper lower sharp upperSharp n hnlo hnhi hodd otherChoice a seeds hseed hprime hcount
  let completion := old.2.2.2.2.2.2
  let cy := Classical.choose (Classical.choose_spec completion)
  let facts := Classical.choose_spec (Classical.choose_spec completion)
  have hgrid := fw_canonical_cy_seed_growth_grids hnlo otherChoice w.family w.p w.oldReference
    w.roles w.network cy facts.2.2.1
  exact ⟨old, facts, w.cross, facts.2.2.1, hgrid.1, hgrid.2.1, hgrid.2.2.1, hgrid.2.2.2⟩

end
end Sude
