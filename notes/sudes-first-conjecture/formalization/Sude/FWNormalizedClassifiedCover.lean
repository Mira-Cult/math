import Sude.FWClassifiedFullCover
import Sude.FWRoleValueUnion

namespace Sude
noncomputable section

/-- Classify the normalized FW keepout using its actual same-square role image. -/
theorem fw_normalized_classified_full_value_cover {n P : ℕ} (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
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
    (a : Cell n ≃ Fin (n*n))
    (batches : ℕ → List DoublePair)
    (candidates : Finset ℕ) (hcard : candidates.card = 17*(6*(n+8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17)
    (blocks : List DoublePair) (stages : List BTSelectedStage) (hlen : stages.length = P)
    (hlenBridge : ∀ j < 5, (batches j).length = 3*(n+8))
    (hkept : kept.card = 16)
    {g : ℕ} {initial final : Finset ℕ} {R last : ℕ}
    (trace : BTGrowingTrace g (6*(n+8)) initial R final last stages)
    (m X w : ℝ) (hX : 100 ≤ X) (hw : 0 ≤ w)
    (hmlo : (243 / 500 : ℝ)*X ≤ m) (hmhi : m ≤ (123 / 250 : ℝ)*X)
    (hmatched : ∀ b ∈ blocks, b.MatchedValid
      (bmorLowBins (fwReflectedLeft m X) (fwReflectedRight m X))
      (bmorHighBins (fwReflectedLeft m X) (fwReflectedRight m X)))
    (hvalues :
      (fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
        Finset.univ.image (btGrowingOffsetCells
          (5*(4*6) + 16*(4*6) + (3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc)).image (entry a) =
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks ∪
        Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint)) :
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5*(4*6) + 16*(4*6) + (3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    let ordinary := fwBridgeSeedProtectedValues batches candidates hcard kept hsub ∪
      Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint)
    let accounted := ordinary ∪ (full \ roles).image (entry a)
    let shielded := doubleBatchLow blocks ∪ doubleBatchHigh blocks
    full.image (entry a) ⊆ accounted ∪ shielded ∧
      accounted.card ≤ 12*(n+8)*5 + 12*(n+8)*254 ∧
      (∀ p ∈ shielded, (p : ℝ) ≤ m-X/4+w*X ∨ m+X/4-w*X ≤ p) := by
  dsimp only
  have hspare := (fw_role_cell_occupancy hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols).2.2.2.2.2.1
  have hroles := hvalues.subset
  simp only [fwWheelWitnessEarlyValues] at hroles
  exact fw_classified_full_value_cover hP a _ _ batches hlenBridge candidates hcard kept hsub hkept
    trace hlen blocks m X w hX hw hmlo hmhi hmatched hroles (le_of_eq hspare)


end
end Sude
