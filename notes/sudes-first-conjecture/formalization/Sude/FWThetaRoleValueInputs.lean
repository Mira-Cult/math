import Sude.FWThetaFamilyWitness
import Sude.FWThetaSameWitnessRoleValues

/-! Conditional candidate, retained-seed and family-image inputs for one
supplied ordered theta-family witness. This record assumes its fields; it does
not assert the existence of a theta witness, a completion, or any result for a
later flow output. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The original selection data and the exact transfers missing from the
family witness, all linked to that very witness and its ordered square. -/
structure FWThetaRoleValueInputs {n L : ℕ} {choice : Fin L → Bool}
    (f : FWThetaFamilyWitness n L choice) (seeds : Finset ℕ) where
  candidates : Finset ℕ
  candidate_card : candidates.card = 17 * (6 * (n + 8))
  kept : Finset ℕ
  kept_sub : kept ⊆ Finset.range 17
  kept_card : kept.card = 16
  candidates_sub : candidates ⊆ seeds
  initial_eq : f.initial = ((poolFinset n).filter (fun p => 43 < p)) \
    fwWheelWitnessEarlyValues f.batches candidates candidate_card kept kept_sub f.blocks
  intermediate : Cell n ≃ Fin (n*n)
  seed_base : Finset.univ.image (fun x => entry f.source
    (fwSeedExistingPairCells f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc x)) =
    retainedSeedEndpoints candidates 17 (6*(n+8)) 2 candidate_card kept kept_sub
  bridge_stage : ∀ j, Finset.univ.image (fun x : (Fin (3*(n+8)) × Fin 2) × Bool =>
    entry intermediate (fwBridgePhysicalDoubleCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc
      ((j,x.1.1,x.1.2),x.2))) =
    Finset.univ.image (fun x : (Fin (3*(n+8)) × Fin 2) × Bool =>
      entry f.source (fwBridgePhysicalDoubleCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc
        ((j,x.1.1,x.1.2),x.2)))
  wide_stage : ∀ j, Finset.univ.image (fun x : (Fin (3*(n+8)) × Fin 2) × Bool =>
    entry intermediate (fwWidePhysicalDoubleCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc
      ((j,x.1.1,x.1.2),x.2))) =
    Finset.univ.image (fun x : (Fin (3*(n+8)) × Fin 2) × Bool =>
      entry f.source (fwWidePhysicalDoubleCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc
        ((j,x.1.1,x.1.2),x.2)))
  seed_intermediate : Finset.univ.image (fun x => entry intermediate
    (fwSeedExistingPairCells f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc x)) =
    retainedSeedEndpoints candidates 17 (6*(n+8)) 2 candidate_card kept kept_sub
  bridge_final : ∀ x, entry f.ordered
      (fwBridgePhysicalDoubleCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc x) =
    entry intermediate (fwBridgePhysicalDoubleCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc x)
  wide_final : ∀ x, entry f.ordered
      (fwWidePhysicalDoubleCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc x) =
    entry intermediate (fwWidePhysicalDoubleCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc x)
  seed_final : ∀ x, entry f.ordered
      (fwSeedExistingPairCells f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc x) =
    entry intermediate (fwSeedExistingPairCells f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc x)

/-- The physical roles of this exact supplied family witness. -/
def fwThetaWitnessRoleCells {n L : ℕ} {choice : Fin L → Bool}
    (f : FWThetaFamilyWitness n L choice) : Finset (Cell n) :=
  fwGrowthEarlyRoleCells f.hrect f.hseedrect f.hwide f.hs choice f.br f.bc f.hbr f.hbc
    f.sr f.sc f.hsr f.hsc f.wr f.wc f.hwr f.hwc ∪
  Finset.univ.image (btGrowingOffsetCells
    (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) f.hoff f.hs choice f.gr f.gc f.hgr f.hgc)

/-- The same ordered and supplied reference squares have exactly the early
selected values plus all growth footprints, given the explicitly supplied
reference image equality. No equality is asserted for a later flow output. -/
theorem fw_theta_role_values_of_inputs {n L : ℕ} {choice : Fin L → Bool}
    (f : FWThetaFamilyWitness n L choice) {seeds : Finset ℕ}
    (w : FWThetaRoleValueInputs f seeds) (reference : Cell n ≃ Fin (n*n))
    (href : (fwThetaWitnessRoleCells f).image (entry reference) =
      (fwThetaWitnessRoleCells f).image (entry f.ordered)) :
    (fwThetaWitnessRoleCells f).image (entry f.ordered) =
        fwWheelWitnessEarlyValues f.batches w.candidates w.candidate_card w.kept w.kept_sub f.blocks ∪
          Finset.univ.biUnion (fun j : Fin f.stages.length => (BTStageTrace.stageAt f.stages rfl j).footprint) ∧
    (fwThetaWitnessRoleCells f).image (entry reference) =
        fwWheelWitnessEarlyValues f.batches w.candidates w.candidate_card w.kept w.kept_sub f.blocks ∪
          Finset.univ.biUnion (fun j : Fin f.stages.length => (BTStageTrace.stageAt f.stages rfl j).footprint) := by
  exact fw_theta_same_witness_role_values f.hrect f.hseedrect f.hwide f.hoff f.hs choice
    f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
    f.batches f.hvalid w.candidates w.candidate_card w.kept w.kept_sub f.blocks f.hlen
    f.trace rfl f.hpool f.source w.intermediate f.ordered reference f.τ
    f.hdiag f.hord w.seed_base f.hplaced w.bridge_stage w.wide_stage w.seed_intermediate
    w.bridge_final w.wide_final w.seed_final f.hgrowthPlace href

end
end Sude
