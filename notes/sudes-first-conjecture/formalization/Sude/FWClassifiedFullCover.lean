import Sude.FWFullSpareCover
import Sude.FWRoleValueBudget
import Sude.FWWideOutsideQuarter
namespace Sude
noncomputable section

/-- Given same-square role-value coverage and a full spare bound, classify all
full-reservation values into a bounded accounted set and the matched wide set.
No physical placement, analytic stock, or numerical gate is inferred. -/
theorem fw_classified_full_value_cover {n P g : ℕ} (hP : P ≤ 238)
    (a : Cell n ≃ Fin (n*n)) (full roles : Finset (Cell n))
    (batches : ℕ → List DoublePair) (hlenBridge : ∀ j < 5, (batches j).length = 3*(n+8))
    (candidates : Finset ℕ) (hcard : candidates.card = 17*(6*(n+8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    {initial final : Finset ℕ} {R last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g (6*(n+8)) initial R final last stages)
    (hlen : stages.length = P)
    (blocks : List DoublePair) (m X w : ℝ) (hX : 100 ≤ X) (hw : 0 ≤ w)
    (hmlo : (243 / 500 : ℝ)*X ≤ m) (hmhi : m ≤ (123 / 250 : ℝ)*X)
    (hmatched : ∀ b ∈ blocks, b.MatchedValid
      (bmorLowBins (fwReflectedLeft m X) (fwReflectedRight m X))
      (bmorHighBins (fwReflectedLeft m X) (fwReflectedRight m X)))
    (hroles : roles.image (entry a) ⊆
      (fwBridgeSeedProtectedValues batches candidates hcard kept hsub ∪
        (doubleBatchLow blocks ∪ doubleBatchHigh blocks)) ∪
        Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint))
    (hspare : (full \ roles).card ≤ 96*(238-P)) :
    let ordinary := fwBridgeSeedProtectedValues batches candidates hcard kept hsub ∪
      Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint)
    let accounted := ordinary ∪ (full \ roles).image (entry a)
    let shielded := doubleBatchLow blocks ∪ doubleBatchHigh blocks
    full.image (entry a) ⊆ accounted ∪ shielded ∧
      accounted.card ≤ 12*(n+8)*5 + 12*(n+8)*254 ∧
      (∀ p ∈ shielded, (p : ℝ) ≤ m-X/4+w*X ∨ m+X/4-w*X ≤ p) := by
  classical
  dsimp only
  let ordinary := fwBridgeSeedProtectedValues batches candidates hcard kept hsub ∪
    Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint)
  let shielded := doubleBatchLow blocks ∪ doubleBatchHigh blocks
  let D := 12*(n+8)*5 + 12*(n+8)*(16+P)
  have hordinary : ordinary.card ≤ D :=
    fw_bridge_seed_growth_card_le batches hlenBridge candidates hcard kept hsub hkept trace hlen
  have hroles' : roles.image (entry a) ⊆ ordinary ∪ shielded := by
    intro p hp
    have hp' := hroles hp
    simp only [ordinary, shielded, Finset.mem_union] at *
    tauto
  have hc := full_value_cover_from_roles_and_spares a full roles ordinary shielded D
    (96*(238-P)) hroles' hordinary hspare
  have hbudget := fw_bridge_prefix_spare_capacity_le n P hP
  have hshield := fw_wide_batch_shielded m X w hX hw hmlo hmhi blocks hmatched
  refine ⟨hc.1, ?_, hshield⟩
  change (ordinary ∪ (full \ roles).image (entry a)).card ≤ _
  calc
    _ ≤ D + 96*(238-P) := hc.2
    _ ≤ 12*(n+8)*5 + 12*(n+8)*254 := by
      simpa [D, Nat.add_assoc] using hbudget
end
end Sude
