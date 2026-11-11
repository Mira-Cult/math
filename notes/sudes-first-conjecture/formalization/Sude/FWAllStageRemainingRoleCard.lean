import Sude.FWCombinedPhysicalStageFamily
import Sude.FWRoleCellOccupancy

/-! Exact cardinality of the remaining actual role cells after all supplied
seed and growth physical stage cells are removed. This makes no assertion
identifying those remaining cells with bridge or wide cell images. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- Under same-square physical placement and joint packing, the complement of
all seed and growth stages in actual roles has the bridge-and-wide count. -/
theorem fw_all_stage_remaining_role_card
    {g n P : ℕ} {initial final : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g (6 * (n + 8)) initial radius final last stages)
    (hlen : stages.length = P) (hpool : ∀ p ∈ initial, p ∈ pool n)
    (earlyValues : Finset ℕ) (hdis : Disjoint initial earlyValues)
    (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254) (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice)
      (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (a : Cell n ≃ Fin (n * n))
    (hseedInj : Function.Injective (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc))
    (hseedValues : ∀ x, entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x) ∈ earlyValues)
    (hplaced : ∀ x : PrefixPhysicalInputs P 6 3 n,
      entry a (btGrowingOffsetCells (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc x) =
        (trace.poolValues hlen hpool (prefixPhysicalInput (by omega) (by omega) x)).val) :
    let offset := 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc)
    let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      offset hoff hs choice gr gc hgr hgc
    let cells := combinedPhysicalPairStageCells seed growth
    (roles \ Finset.univ.biUnion cells).card = 12 * (5 + 3 * (n / 450)) * (n + 8) := by
  classical
  dsimp only
  let offset := 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)
  let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
    Finset.univ.image (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc)
  let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
  let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
    offset hoff hs choice gr gc hgr hgc
  let cells := combinedPhysicalPairStageCells seed growth
  have hfam := fw_combined_physical_stage_family trace hlen hpool earlyValues hdis
    hrect hseed hwide offset hoff hs choice br bc sr sc wr wc gr gc
    hbr hbc hsr hsc hwr hwc hgr hgc a hseedInj hseedValues hplaced
  dsimp only at hfam
  have hocc := fw_role_cell_occupancy hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  dsimp only at hocc
  have hsub : Finset.univ.biUnion cells ⊆ roles := hfam.2.2.2 Finset.univ
  have hcard : ∀ j, (cells j).card = 12 * (n + 8) := hfam.2.1
  have hrole : roles.card = 12 * (5 + 16 + 3 * (n / 450) + P) * (n + 8) := hocc.2.1
  have hstage : (Finset.univ.biUnion cells).card = (16 + P) * (12 * (n + 8)) := by
    have hdis' : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin 16 ⊕ Fin P)) : Set _) cells := by
      simpa only [Finset.coe_univ] using hfam.1
    rw [Finset.card_biUnion hdis']
    simp [hcard]
  have h := Finset.card_sdiff_add_card_eq_card hsub
  rw [hstage, hrole] at h
  nlinarith

end
end Sude
