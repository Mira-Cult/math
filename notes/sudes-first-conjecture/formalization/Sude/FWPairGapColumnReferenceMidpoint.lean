import Sude.FWPairGapColumnMidpointGapInvoice

/-! Conditional conversion of a supplied centered-reference invoice and the
ordered-square FW column midpoint identity to one physical-column comparison.
No completion, numeric line bound, or later flow is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

/-- The supplied reference column is within 9/2 of the ordered-square
bridge/wide midpoint scores, their original-source means and one remaining-cell
sum. Matching and signed gap hypotheses apply to `new`; the invoice applies
to the same `vc` and `network`. -/
theorem fw_pair_gap_column_reference_midpoint_comparison {n : ℕ}
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
    (c : Fin n) (reference : Cell n ≃ Fin (n*n))
    (hinvoice : |2 * (columnSum reference c : ℤ) - physicalNetworkMidpointTwice vc network c| ≤ 9) :
    let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    let col := (Finset.univ : Finset (Fin n)).image (fun r => (r,c))
    let line := fun z : Cell n => z.2 = c
    |(columnSum reference c : ℝ) -
      ((doubleBlockActualCenteredScore bridge line base new +
        (∑ j, ∑ b, doubleBlockLineWeight bridge line j b * doubleStageMidpointMean bridge base j)) +
       (doubleBlockActualCenteredScore wide line base new +
        (∑ j, ∑ b, doubleBlockLineWeight wide line j b * doubleStageMidpointMean wide base j)) +
       (∑ z ∈ col \ (Finset.univ.image bridge ∪ Finset.univ.image wide), (entry new z : ℝ)))| ≤ (9 : ℝ)/2 := by
  classical
  dsimp only
  have hid := fw_pair_gap_bridge_wide_column_midpoint_of_gap_invoice
    hP hrect hseed hwide hfull offset hoff hs choice br bc sr sc wr wc gr gc
    hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols base new hpairgap hseedgap
    vr vc network hslotr hslotc blocksR hblockr hblockc gapb gapw hinvoiceb hinvoicew c
  have hr : |2 * (columnSum reference c : ℝ) - (physicalNetworkMidpointTwice vc network c : ℝ)| ≤ 9 := by
    exact_mod_cast hinvoice
  dsimp only at hid
  rw [hid] at hr
  rw [abs_le] at hr ⊢
  constructor <;> linarith [hr.1, hr.2]

end
end Sude
