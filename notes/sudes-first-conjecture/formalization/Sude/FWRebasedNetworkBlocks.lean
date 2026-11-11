import Sude.FWReferenceCompletionTransport
import Sude.FWBridgeWideNetworkMatching

/-! Transport actual FW network slots and block labels to a completion fixing
the same geometric reservation. No reference, flow, or numerical bound is
constructed. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1500000

/-- The FW rebase uses the same row and transposed-column slots, edge blocks,
radii, and pair gaps. Fixedness is supplied on the complete reservation; its
containment of all active roles and network slots is proved from the packing. -/
theorem fw_rebased_network_blocks {n P : ℕ} (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n) (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (a c : Cell n ≃ Fin (n*n))
    (vr : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) a)
    (vc : RowNetworkPairs (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) (LayerPacking.transposePlacement a))
    (BR : CenteredNetwork (Fin 3 × Fin n) _ vr) (BC : CenteredNetwork (Fin 3 × Fin n) _ vc)
    (hslotr : ∀ t side, rowNetworkSlot vr (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side)
    (hslotc : ∀ t side, rowNetworkSlot vc (t,side) = layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side)
    (hblockr : ∀ edge, BR.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2)))
    (hblockc : ∀ edge, BC.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex bc sc wc gc hbc hsc hwc hgc ((x,edge.1),edge.2)))
    (hfixed : ∀ x ∈ packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc)), entry c x = entry a x) :
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    roles ⊆ full ∧
    ∃ hr : ∀ k side, entry c (rowNetworkSlot vr (k,side)) = entry a (rowNetworkSlot vr (k,side)),
    ∃ hc : ∀ k side, entry (LayerPacking.transposePlacement c) (rowNetworkSlot vc (k,side)) =
      entry (LayerPacking.transposePlacement a) (rowNetworkSlot vc (k,side)),
      (∀ t side, rowNetworkSlot (rowNetworkPairsRebase vr c hr) (t,side) =
        layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side) ∧
      (∀ t side, rowNetworkSlot (rowNetworkPairsRebase vc (LayerPacking.transposePlacement c) hc) (t,side) =
        layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side) ∧
      (∀ edge, (centeredNetworkRebase vr BR c hr).block edge =
        (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
          (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2))) ∧
      (∀ edge, (centeredNetworkRebase vc BC (LayerPacking.transposePlacement c) hc).block edge =
        (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
          (fun x => fwJointActualGridPairIndex bc sc wc gc hbc hsc hwc hgc ((x,edge.1),edge.2))) ∧
      (∀ k, (rowNetworkPairsRebase vr c hr).gap k = vr.gap k) ∧
      (∀ k, (rowNetworkPairsRebase vc (LayerPacking.transposePlacement c) hc).gap k = vc.gap k) ∧
      (∀ edge, (centeredNetworkRebase vr BR c hr).radius edge = BR.radius edge) ∧
      (∀ edge, (centeredNetworkRebase vc BC (LayerPacking.transposePlacement c) hc).radius edge = BC.radius edge) := by
  classical
  dsimp only
  have hg := fw_role_support_for_trace_networks hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  dsimp only at hg
  refine ⟨hg.2.2.1, ?_⟩
  have hr (k : Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) (side : Bool) :
      entry c (rowNetworkSlot vr (k,side)) = entry a (rowNetworkSlot vr (k,side)) := by
    apply hfixed
    rw [hslotr]
    exact hg.2.2.1 (hg.1 (layerPairSlot_mem _ k side))
  have hc (k : Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) (side : Bool) :
      entry (LayerPacking.transposePlacement c) (rowNetworkSlot vc (k,side)) =
        entry (LayerPacking.transposePlacement a) (rowNetworkSlot vc (k,side)) := by
    change entry c (rowNetworkSlot vc (k,side)).swap = entry a (rowNetworkSlot vc (k,side)).swap
    apply hfixed
    rw [hslotc]
    exact hg.2.2.1 (hg.2.1 (transposedLayerPairSlot_mem _ k side))
  refine ⟨hr, hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hslotr
  · exact hslotc
  · exact hblockr
  · exact hblockc
  · intro k; rfl
  · intro k; rfl
  · intro edge; rfl
  · intro edge; rfl

end
end Sude
