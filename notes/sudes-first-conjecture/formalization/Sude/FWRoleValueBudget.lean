import Sude.FWEarlyReservationCard
import Sude.FWBridgeSeedWideRolePreservation
import Sude.BTGrowingFootprintCoverage
import Sude.BTGrowingExactStock
namespace Sude
noncomputable section

/-- Bridge and retained seed values occupy at most their full endpoint budgets. -/
theorem fw_bridge_retained_seed_card_le {n : ℕ} (batches : ℕ → List DoublePair)
    (hlen : ∀ j < 5, (batches j).length = 3 * (n + 8))
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16) :
    (fwBridgeSeedProtectedValues batches candidates hcard kept hsub).card ≤
      12*(n+8)*5 + 12*(n+8)*16 := by
  classical
  let bridge := priorBridgeReservation ∅ (Finset.range 5) batches
  let seed := retainedSeedEndpoints candidates 17 (6*(n+8)) 2 hcard kept hsub
  have hb : bridge.card ≤ 2 * (6 * (n+8)) * 5 := fw_five_bridge_reservation_card_le n batches hlen
  have hs : seed.card ≤ 2 * (6 * (n+8)) * 16 := by
    dsimp [seed, retainedSeedEndpoints]
    have hi := Finset.card_image_le (s := retainedSeedLabels 17 (6*(n+8)) kept hsub)
      (f := sortedSeedEndpoint candidates 17 (6*(n+8)) 2 hcard)
    rw [retainedSeedLabels_card, hkept] at hi
    exact hi
  have hu := Finset.card_union_le bridge seed
  change (bridge ∪ seed).card ≤ _
  nlinarith

/-- The exact indexed footprint union has 2*Q endpoints per stage; no pool hypothesis is needed. -/
theorem growing_indexed_footprint_card
    {g Q : ℕ} {initial final : Finset ℕ} {R last : ℕ}
    {stages : List BTSelectedStage} (trace : BTGrowingTrace g Q initial R final last stages)
    {P : ℕ} (hlen : stages.length = P) :
    (Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint)).card = 2 * Q * P := by
  classical
  let U := Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint)
  have hsub : U ⊆ initial := by
    intro x hx
    obtain ⟨j, _, hxj⟩ := Finset.mem_biUnion.mp hx
    exact trace.footprints_subset _ (BTStageTrace.stageAt_mem stages hlen j) hxj
  have hfinal : final = initial \ U := trace.final_eq_initial_sdiff_indexed_footprints hlen
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  rw [← hfinal] at hc
  change final.card + U.card = initial.card at hc
  change U.card = _
  have ht := trace.final_accounting.2.1
  rw [hlen] at ht
  omega

/-- The FW trace uses six times n+8 endpoint pairs at each stage. -/
theorem fw_growing_indexed_footprint_card
    {g n : ℕ} {initial final : Finset ℕ} {R last : ℕ}
    {stages : List BTSelectedStage} (trace : BTGrowingTrace g (6*(n+8)) initial R final last stages)
    {P : ℕ} (hlen : stages.length = P) :
    (Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint)).card = 12 * (n+8) * P := by
  rw [growing_indexed_footprint_card trace hlen]
  ring

/-- Actual bridge, retained-seed and growth value union on the supplied trace.
No wide values, spare cells or between-family disjointness are assumed. -/
theorem fw_bridge_seed_growth_card_le {n P g : ℕ}
    (batches : ℕ → List DoublePair) (hlenBridge : ∀ j < 5, (batches j).length = 3*(n+8))
    (candidates : Finset ℕ) (hcard : candidates.card = 17*(6*(n+8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    {initial final : Finset ℕ} {R last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g (6*(n+8)) initial R final last stages)
    (hlen : stages.length = P) :
    (fwBridgeSeedProtectedValues batches candidates hcard kept hsub ∪
      Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint)).card ≤
      12*(n+8)*5 + 12*(n+8)*(16+P) := by
  have hb := fw_bridge_retained_seed_card_le batches hlenBridge candidates hcard kept hsub hkept
  have hg := fw_growing_indexed_footprint_card trace hlen
  have hu := Finset.card_union_le (fwBridgeSeedProtectedValues batches candidates hcard kept hsub)
    (Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint))
  nlinarith

/-- Transfer this upper bound to supplied physical cells on one square when
its actual entry image is covered by the exact same witness value sets. -/
theorem fw_physical_bridge_seed_growth_card_le {n P g : ℕ}
    (a : Cell n ≃ Fin (n*n)) (cells : Finset (Cell n))
    (batches : ℕ → List DoublePair) (hlenBridge : ∀ j < 5, (batches j).length = 3*(n+8))
    (candidates : Finset ℕ) (hcard : candidates.card = 17*(6*(n+8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    {initial final : Finset ℕ} {R last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g (6*(n+8)) initial R final last stages)
    (hlen : stages.length = P)
    (himage : cells.image (entry a) ⊆ fwBridgeSeedProtectedValues batches candidates hcard kept hsub ∪
      Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint)) :
    (cells.image (entry a)).card ≤ 12*(n+8)*5 + 12*(n+8)*(16+P) := by
  exact (Finset.card_le_card himage).trans
    (fw_bridge_seed_growth_card_le batches hlenBridge candidates hcard kept hsub hkept trace hlen)
end
end Sude
