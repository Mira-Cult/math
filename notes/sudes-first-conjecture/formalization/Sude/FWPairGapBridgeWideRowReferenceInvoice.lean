import Sude.FWPairGapBridgeWideRowMidpoint

/-! Conditional row invoice for a supplied centered reference square. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

/-- The exact same-square midpoint identity and the supplied doubled reference
invoice give a half-unit-scaled error bound. The complement remains explicit;
no complete-line or subsequent flow bound is asserted. -/
theorem fw_pair_gap_bridge_wide_row_reference_invoice
    {n : ℕ} {stages : List BTSelectedStage}
    (hP : stages.length ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + stages.length * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n) (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (source new : Cell n ≃ Fin (n*n))
    (hpairgap : ∀ j i, entry new (btGrowingOffsetPairCells
      (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc ((j,i),true)) =
      entry new (btGrowingOffsetPairCells
        (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc ((j,i),false)) + (stages.get j).gap)
    (hseedgap : ∀ j q, entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),true)) =
       entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),false)) + 2)
    (vr : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) new)
    (vc : RowNetworkPairs (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) (LayerPacking.transposePlacement new))
    (networkR : CenteredNetwork (Fin 3 × Fin n) (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) vr)
    (blocksC : (Fin 3 × Fin n) → Finset (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n))
    (hslotr : ∀ t side, rowNetworkSlot vr (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side)
    (hslotc : ∀ t side, rowNetworkSlot vc (t,side) = layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side)
    (hblockr : ∀ edge, networkR.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2)))
    (hblockc : ∀ edge, blocksC edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex bc sc wc gc hbc hsc hwc hgc ((x,edge.1),edge.2)))
    (reference : Cell n ≃ Fin (n*n)) (r : Fin n)
    (hinvoice : |2 * (rowSum reference r : ℝ) -
      (physicalNetworkMidpointTwice vr networkR r : ℝ)| ≤ 9) :
    let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    let Ab := Finset.univ.image bridge
    let Aw := Finset.univ.image wide
    let row := (Finset.univ : Finset (Fin n)).image (fun c => (r,c))
    let line := fun c : Cell n => c.1 = r
    |(rowSum reference r : ℝ) -
      ((doubleBlockActualCenteredScore bridge line source new +
        (∑ j, ∑ b, doubleBlockLineWeight bridge line j b * doubleStageMidpointMean bridge source j)) +
       (doubleBlockActualCenteredScore wide line source new +
        (∑ j, ∑ b, doubleBlockLineWeight wide line j b * doubleStageMidpointMean wide source j)) +
       (∑ c ∈ row \ (Ab ∪ Aw), (entry new c : ℝ)))| ≤ (9 : ℝ) / 2 := by
  classical
  have hmid := fw_pair_gap_bridge_wide_row_midpoint hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
    source new hpairgap hseedgap vr vc networkR blocksC hslotr hslotc hblockr hblockc r
  dsimp only at hmid ⊢
  rw [hmid] at hinvoice
  have h := abs_le.mp hinvoice
  apply abs_le.mpr
  constructor <;> linarith

end
end Sude
