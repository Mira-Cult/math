import Sude.FWCanonicalFamilyRelabel
import Sude.FWCanonicalCYSeedGrowthGrid
import Sude.FWThetaBridgeSourceGap
import Sude.FWThetaWideSourceGap

/-! Pointwise alignment of the actual canonical rectangle gap with the
stage-permuted abstract source gaps on the exact finite support. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
local instance fwCanonicalFamilyGapAlignmentStageDecidable : DecidableEq BTSelectedStage := Classical.decEq _

/-- The destination block used by one canonical choice side. -/
def fwCanonicalFamilyDestination {n : ℕ} (side : Bool) : Fin (3*(n+8)) :=
  Fin.castLE (by omega : 4*6 ≤ 3*(n+8)) (fwCanonicalChoiceRectangle side)

/-- The abstract gap uses the actual source chosen by each stage permutation. -/
def fwCanonicalFamilySourceGap {n L : ℕ} {choice : Fin L → Bool}
    (f : FWThetaFamilyWitness n L choice) (side : Bool) :
    Sum (Sum (Sum (Fin 16) BTSelectedStage) ℕ) (Fin (3*(n/450))) → ℕ :=
  let d := fwCanonicalFamilyDestination (n := n) side
  Sum.elim (fwStageVaryingJoinedBridgeGap fwSeedTraceGap f.batches
      (fwPermutedBridgeIndex f.πb d))
    (fun j => fwPermutedWideSourceGap f.blocks f.hlen f.πw j d)

/-- Every represented physical label has the precise stage-permuted abstract
source gap on the same ordered family witness. -/
theorem fw_canonical_family_gap_alignment {n : ℕ}
    {choice : Fin (fwJointRectangleCount n 254) → Bool}
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice) (side : Bool)
    (x : {x // x ∈ fwCanonicalFamilySourceSupport f}) :
    fwOrderedCanonicalRectangleGap f (fwCanonicalFamilyLabel f side x) =
      fwCanonicalFamilySourceGap f side x.val := by
  classical
  rcases x with ⟨x, hx⟩
  cases x with
  | inl x =>
    cases x with
    | inl a =>
      change fwOrderedCanonicalRectangleGap f
        (fwCanonicalSeedGrowthLabel f side ⟨a, (fw_canonical_family_source_seed_mem f a).1 hx⟩) =
          fwSeedTraceGap a
      exact fw_canonical_seed_growth_label_gap f side _
    | inr j =>
      let jj : Fin 5 := ⟨j, (fw_canonical_family_source_bridge_mem f j).1 hx⟩
      have h := (fw_ordered_canonical_rectangle_gap f).1 jj (fwCanonicalChoiceRectangle side)
      rw [fw_theta_bridge_source_gap] at h
      simpa [fwCanonicalFamilyLabel, fwCanonicalFamilySourceGap, fwStageVaryingJoinedBridgeGap,
        fwPermutedBridgeIndex, fwCanonicalFamilyDestination, jj,
        (fw_canonical_family_source_bridge_mem f j).1 hx] using h
  | inr j =>
    have h := (fw_ordered_canonical_rectangle_gap f).2.2.1 j (fwCanonicalChoiceRectangle side)
    rw [fw_theta_wide_source_gap] at h
    simpa [fwCanonicalFamilyLabel, fwCanonicalFamilySourceGap, fwCanonicalFamilyDestination] using h

end
end Sude
