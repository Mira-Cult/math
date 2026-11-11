import Sude.FWPairGapBridgeWideColumnMidpoint
import Sude.DoubleBlockPairedGapEquality

/-! The common natural gap per block invoice discharges the paired-gap
hypotheses in the conditional same-square column midpoint identity. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

/-- The supplied block invoices and growth pair gaps are on the same final
square `new`; no equality with the reference `base` is assumed. -/
theorem fw_pair_gap_bridge_wide_column_midpoint_of_gap_invoice {n : ℕ}
    {stages : List BTSelectedStage}
    (hP : stages.length ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hfull : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + stages.length * (4 * 6) ≤ fwJointRectangleCount n 254)
    (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (base new : Cell n ≃ Fin (n*n))
    (hpairgap : ∀ j i, entry new (btGrowingOffsetPairCells
      (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      offset hoff hs choice gr gc hgr hgc ((j,i),true)) =
      entry new (btGrowingOffsetPairCells
        (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
        offset hoff hs choice gr gc hgr hgc ((j,i),false)) + (stages.get j).gap)
    (hseedgap : ∀ j q, entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),true)) =
       entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),false)) + 2)
    (vr : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) new)
    (vc : RowNetworkPairs (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) (LayerPacking.transposePlacement new))
    (network : CenteredNetwork (Fin 3 × Fin n) (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) vc)
    (hslotr : ∀ t side, rowNetworkSlot vr (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side)
    (hslotc : ∀ t side, rowNetworkSlot vc (t,side) = layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side)
    (blocksR : (Fin 3 × Fin n) → Finset (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n))
    (hblockr : ∀ edge, blocksR edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2)))
    (hblockc : ∀ edge, network.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex bc sc wc gc hbc hsc hwc hgc ((x,edge.1),edge.2)))
    (gapb : Fin 5 → Fin (3 * (n + 8)) → ℕ)
    (gapw : Fin (3 * (n / 450)) → Fin (3 * (n + 8)) → ℕ)
    (hinvoiceb : ∀ j b p,
      entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,b,p),true)) =
      entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,b,p),false)) + gapb j b)
    (hinvoicew : ∀ j b p,
      entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),true)) =
      entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),false)) + gapw j b)
    (c : Fin n) :
    let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    let col := (Finset.univ : Finset (Fin n)).image (fun r => (r,c))
    let line := fun z : Cell n => z.2 = c
    (physicalNetworkMidpointTwice vc network c : ℝ) =
      (2 * doubleBlockActualCenteredScore bridge line base new +
        2 * (∑ j, ∑ b, doubleBlockLineWeight bridge line j b * doubleStageMidpointMean bridge base j)) +
      (2 * doubleBlockActualCenteredScore wide line base new +
        2 * (∑ j, ∑ b, doubleBlockLineWeight wide line j b * doubleStageMidpointMean wide base j)) +
      2 * (∑ z ∈ col \ (Finset.univ.image bridge ∪ Finset.univ.image wide), (entry new z : ℝ)) := by
  classical
  have hb := double_block_paired_gap_equality
    (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc) new gapb hinvoiceb
  have hw := double_block_paired_gap_equality
    (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc) new gapw hinvoicew
  exact fw_pair_gap_bridge_wide_column_midpoint hP hrect hseed hwide hfull
    offset hoff hs choice br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
    base new hpairgap hseedgap vr vc network hslotr hslotc blocksR hblockr hblockc
    (fun j rect => hb j (Fin.castLE (by omega) rect))
    (fun j rect => hw j (Fin.castLE (by omega) rect)) c

end
end Sude
