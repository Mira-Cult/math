import Sude.PhysicalAllLineWeights
import Sude.FWSeedReferenceCenteredScore
import Sude.FWSeedPairMidpointTransfer
import Sude.FWBridgePairMidpointTransfer
import Sude.FWWidePairMidpointTransfer
import Sude.DoubleBlockMidpointScoreTransfer

/-! Midpoint score preservation for the early seed, bridge and wide families
on one supplied fresh reference. Signed gap orientations and later flow
switches remain separate. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- Fixed rectangle cells and pair sums for the actual joint row and column
network pairs preserve all early-family midpoint scores on the same fresh
reference. Seed means use `grown`; bridge and wide means use the distinct
source `source`. The ordered pre-centering placement is explicit. -/
theorem fw_early_reference_midpoint_scores {n L : ℕ}
    (hrect : 5*(4*6) ≤ L)
    (hseed : 5*(4*6) + 16*(4*6) ≤ L)
    (hwide : 5*(4*6) + 16*(4*6) + (3*(n/450))*(4*6) ≤ L)
    (hs : 2*L+1 ≤ n) (choice : Fin L → Bool)
    (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5*3) (hbc : bc.length = 5*3)
    (hsr : sr.length = 16*3) (hsc : sc.length = 16*3)
    (hwr : wr.length = (3*(n/450))*3) (hwc : wc.length = (3*(n/450))*3)
    (grown source ordered fresh : Cell n ≃ Fin (n*n))
    (ω : Fin 16 → Equiv.Perm (Fin (6*(n+8))))
    (hplaced : ∀ j i side,
      entry ordered (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),side)) =
        entry grown (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,ω j i),side)))
    (hfixed : ∀ c ∈ packedRectangleSupport hs choice, entry fresh c = entry ordered c)
    (hrow : ∀ k, entry fresh (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k false) +
        entry fresh (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k true) =
      entry ordered (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k false) +
        entry ordered (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k true))
    (hcol : ∀ k, entry fresh ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k false).swap) +
        entry fresh ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k true).swap) =
      entry ordered ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k false).swap) +
        entry ordered ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k true).swap)) :
    let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    let line := fun l : Fin ((n+n)+2) => fun c => c ∈ physicalAllLineCells l
    let weights := fun l j i => physicalPairLineWeight seed (line l) (j,i)
    let values := fun j i => (((entry grown (seed ((j,i),false)) : ℝ) +
      entry grown (seed ((j,i),true))) / 2)
    ∀ l : Fin ((n+n)+2),
      stageLineCentered (fun _ _ => Finset.univ) weights values l ω =
        (∑ j, ∑ i, weights l j i *
          (((((entry fresh (seed ((j,i),false)) : ℝ) + entry fresh (seed ((j,i),true))) / 2)) -
            ((∑ q, values j q) / (6*(n+8) : ℕ)))) ∧
      doubleBlockActualCenteredScore bridge (line l) source fresh =
        doubleBlockActualCenteredScore bridge (line l) source ordered ∧
      doubleBlockActualCenteredScore wide (line l) source fresh =
        doubleBlockActualCenteredScore wide (line l) source ordered := by
  classical
  dsimp only
  let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
  let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
  let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
  let line : Fin ((n+n)+2) → Cell n → Prop := fun l c => c ∈ physicalAllLineCells l
  let weights := fun l j i => physicalPairLineWeight seed (line l) (j,i)
  let values := fun j i => (((entry grown (seed ((j,i),false)) : ℝ) +
    entry grown (seed ((j,i),true))) / 2)
  have hseedmid := fw_seed_pair_midpoint_transfer hseed hs choice br sr wr gr bc sc wc gc hsr hsc
    ordered fresh hfixed hrow hcol
  have hbridgemid := fw_bridge_pair_midpoint_transfer hrect hs choice br sr wr gr bc sc wc gc hbr hbc
    ordered fresh hfixed hrow hcol
  have hwidemid := fw_wide_pair_midpoint_transfer hwide hs choice br sr wr gr bc sc wc gc hwr hwc
    ordered fresh hfixed hrow hcol
  intro l
  refine ⟨?_, ?_, ?_⟩
  · simpa [seed, line, weights, values] using
      (fw_seed_reference_centered_score hseed hs choice sr sc hsr hsc grown ordered fresh ω
        (fun _ _ => Finset.univ) weights hplaced hseedmid l)
  · exact double_block_midpoint_score_transfer bridge (line l) source ordered fresh hbridgemid
  · apply double_block_midpoint_score_transfer wide (line l) source ordered fresh
    simpa [doubleBlockPairMidpoint] using hwidemid

end
end Sude
