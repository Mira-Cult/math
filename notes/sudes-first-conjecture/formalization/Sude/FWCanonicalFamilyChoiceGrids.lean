import Sude.FWCanonicalFamilyGapAlignment
import Sude.FWPermutedBridgeWideGrid
import Sude.ChoiceFiberGridRelabel

/-! Physical choice grids using exactly one same-witness representative from
each realized family. Crossing, pool-mean and size bounds are supplied. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
local instance fwCanonicalFamilyChoiceGridsStageDecidable : DecidableEq BTSelectedStage := Classical.decEq _

/-- The exact side-dependent radius, with actual stage-permuted bridge and
wide source gaps and the seed/growth trace radius. -/
def fwCanonicalFamilyRadius {n L : ℕ} {choice : Fin L → Bool}
    (f : FWThetaFamilyWitness n L choice) (side : Bool) : ℕ :=
  let d := fwCanonicalFamilyDestination (n := n) side
  f.last + (∑ j ∈ Finset.range 5,
      selectedBridgeGap f.batches (fwPermutedBridgeIndex f.πb d j) j) +
    ∑ j, fwPermutedWideSourceGap f.blocks f.hlen f.πw j d

/-- Both choice fibers have complete even grids at their own literal source
radii. The physical gap is computed on the same supplied ordered witness. -/
theorem fw_canonical_family_choice_grids {n : ℕ} (hnlo : 19485 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254)
      (fwSelectedThetaChoice hnlo otherChoice))
    (hcross : (poolMaximum n : ℝ) / 23 ≤ f.last)
    (hX : (100 : ℝ) ≤ poolMaximum n)
    (hmlo : (243 / 500 : ℝ) * poolMaximum n ≤ (Lucas.poolTotal n : ℝ) / (n*n : ℕ))
    (hmhi : (Lucas.poolTotal n : ℝ) / (n*n : ℕ) ≤ (123 / 250 : ℝ) * poolMaximum n) :
    ∀ side, CompleteEvenGrid
      ((fwActiveRectangleLabels n f.stages.length f.stageCap).filter
        fun i => fwSelectedThetaChoice hnlo otherChoice i = side)
      (fwOrderedCanonicalRectangleGap f) (fwCanonicalFamilyRadius f side) ∧
      2 ∣ fwCanonicalFamilyRadius f side := by
  classical
  have hseed := fw_seed_trace_even_grid_unconditional_coverage (by omega) f.trace
  have hsource (side : Bool) :
      CompleteEvenGrid (fwCanonicalFamilySourceSupport f) (fwCanonicalFamilySourceGap f side)
        (fwCanonicalFamilyRadius f side) ∧ 2 ∣ fwCanonicalFamilyRadius f side := by
    have h := fw_permuted_bridge_wide_source_grid ∅ f.batches f.hvalid f.πb f.πw
      (fwCanonicalFamilyDestination (n := n) side)
      (fwSeedTraceLabels f.stages) fwSeedTraceGap f.last hseed.1 hseed.2 hcross
      ((Lucas.poolTotal n : ℝ) / (n*n : ℕ)) hX hmlo hmhi f.blocks f.hlen f.hmatched
    exact ⟨by simpa only [fwCanonicalFamilySourceSupport, fwCanonicalFamilySourceGap,
        fwCanonicalFamilyRadius] using h.2.2.2.2.1,
      by simpa only [fwCanonicalFamilyRadius] using h.2.2.2.2.2.1⟩
  have hphys := choice_fiber_complete_even_grids
    (fun _ => fwCanonicalFamilySourceSupport f) (fwCanonicalFamilySourceGap f)
    (fwCanonicalFamilyRadius f) (fwActiveRectangleLabels n f.stages.length f.stageCap)
    (fwSelectedThetaChoice hnlo otherChoice) (fwOrderedCanonicalRectangleGap f)
    (fwCanonicalFamilyLabel f)
    (fun side => (fw_canonical_family_label_embedding hnlo otherChoice f side).1)
    (fun side x => ⟨((fw_canonical_family_label_embedding hnlo otherChoice f side).2 x).1,
      ((fw_canonical_family_label_embedding hnlo otherChoice f side).2 x).2,
      fw_canonical_family_gap_alignment f side x⟩)
    (fun side => (hsource side).1)
  intro side
  exact ⟨hphys side, (hsource side).2⟩

end
end Sude
