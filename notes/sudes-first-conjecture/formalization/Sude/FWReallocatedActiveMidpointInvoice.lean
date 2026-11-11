import Sude.FWReallocatedPhysicalMidpoints
import Sude.FWPhysicalMidpointInvoice
import Sude.FWReallocatedSeedEdgeGap
import Sude.ActiveSupportCenteredInvoice
import Sude.FWRoleSupportEquality

/-! A fresh active-role reference over supplied reallocated networks, with
physical midpoint comparison. The placement, geometry, network and trace
are explicit inputs; no theta existence or concentration transfer is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

theorem fw_reallocated_active_role_fresh_midpoint_invoice {n Q : ℕ}
    (p : Fin 3 → Equiv.Perm (Fin n))
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (hrect : 5 * (4 * 6) ≤ (fwJointRectangleCount n 254)) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ (fwJointRectangleCount n 254))
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ (fwJointRectangleCount n 254))
    (hs : 2 * (fwJointRectangleCount n 254) + 1 ≤ n) (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc : List (LayerPacking.Layer n)) (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3) (old grown b : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hr hc sr sc hsr hsc wr wc hwr hwc,
      entry grown c = entry old c)
    (hplace : ∀ x, entry old (fwBridgeLayerCells br bc hr hc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x))
    (hbridge : ∀ x, entry b (fwBridgeLayerCells br bc hr hc x) = entry grown (fwBridgeLayerCells br bc hr hc x))
    (hwidePreserved : ∀ x : FWWideInputs n,
      entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) = entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x))
    (hseedNew : ∀ j i, entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i), true)) =
      entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i), false)) + 2)
    {initial final : Finset ℕ} {last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 Q initial 32 final last stages)
    (hP : stages.length ≤ 238)
    (hoff : (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) +
      stages.length * (4 * 6) ≤ fwJointRectangleCount n 254)
    (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (hgrowthPreserved : ∀ (edge : Fin 3 × Fin n) (network : Bool) i side,
      entry b (fwGrowthEdgeCells (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc edge network i side) =
      entry grown (fwGrowthEdgeCells (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc edge network i side))
    (hgrowthOld : ∀ (edge : Fin 3 × Fin n) (network : Bool) i,
      entry grown (fwGrowthEdgeCells (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc edge network i true) =
      entry grown (fwGrowthEdgeCells (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc edge network i false) +
        (BTStageTrace.stageAt stages rfl i).gap)
    (wide : (Fin 3 × Fin n) → Fin (3 * (n / 450)) → ℕ)
    (hwideOld : ∀ (edge : Fin 3 × Fin n) (j : Fin (3 * (n / 450))) (network : Bool),
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide edge j)
    (rect : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers rect (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc))
    (hrowGap : ∀ i e, entry b (((((br ++ sr) ++ wr) ++ gr).get i).1 e,
        ((((br ++ sr) ++ wr) ++ gr).get i).2 e) =
      entry b (e, ((((br ++ sr) ++ wr) ++ gr).get i).2 e) +
        fwPhysicalRowLayerGap b (((br ++ sr) ++ wr) ++ gr) i e)
    (hcolGap : ∀ i e, entry b (((((bc ++ sc) ++ wc) ++ gc).get i).2 e,
        ((((bc ++ sc) ++ wc) ++ gc).get i).1 e) =
      entry b (((((bc ++ sc) ++ wc) ++ gc).get i).2 e, e) +
        fwPhysicalColumnLayerGap b (((bc ++ sc) ++ wc) ++ gc) i e)
    (BR : CenteredNetwork (Fin 3 × Fin n) (Fin ((((br ++ sr) ++ wr) ++ gr).length) × Fin n)
      (hrows.rowPairs b (fwPhysicalRowLayerGap b (((br ++ sr) ++ wr) ++ gr)) hrowGap))
    (BC : CenteredNetwork (Fin 3 × Fin n) (Fin ((((bc ++ sc) ++ wc) ++ gc).length) × Fin n)
      (hcols.columnPairs b (fwPhysicalColumnLayerGap b (((bc ++ sc) ++ wc) ++ gc)) hcolGap))
    (hends : ∀ e, BR.source e = e.2 ∧ BC.source e = e.2 ∧
      BR.target e = p e.1 e.2 ∧ BC.target e = p e.1 e.2)
    (hblockR : ∀ edge, BR.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)))
    (hblockC : ∀ edge, BC.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)))
    (hradius : ∀ edge, BR.radius edge = last +
      (∑ j ∈ Finset.range 5, selectedBridgeGap batches
        (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge) j) + ∑ j, wide edge j)
    (hsame : ∀ edge, BC.radius edge = BR.radius edge)
    (N : ℕ) (hR : ∀ e, 2 * N ≤ BR.radius e) (hC : ∀ e, 2 * N ≤ BC.radius e) :
    let rowLayers := ((br ++ sr) ++ wr) ++ gr
    let colLayers := ((bc ++ sc) ++ wc) ++ gc
    let rowGap := fwPhysicalRowLayerGap b rowLayers
    let colGap := fwPhysicalColumnLayerGap b colLayers
    let source : Fin 3 × Fin n → Fin n := fun e => e.2
    let target : Fin 3 × Fin n → Fin n := fun e => p e.1 e.2
    let active := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hr hc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
    ∃ b₀ : Cell n ≃ Fin (n*n),
      TwoNetworkReferenceInvoice b b₀ rowLayers colLayers hrows hcols rowGap colGap hrowGap hcolGap BR BC ∧
      (∀ r, |2 * (rowSum b₀ r : ℤ) -
        physicalNetworkMidpointTwice (hrows.rowPairs b rowGap hrowGap) BR r| ≤ 9) ∧
      (∀ c, |2 * (columnSum b₀ c : ℤ) -
        physicalNetworkMidpointTwice (hcols.columnPairs b colGap hcolGap) BC c| ≤ 9) ∧
      mainSum b₀ = mainSum b ∧ antiSum b₀ = antiSum b ∧
      (∀ c ∈ rect, entry b₀ c = entry b c) ∧
      (∀ c ∉ active, entry b₀ c = entry b c) ∧
      active.image (entry b₀) = active.image (entry b) ∧
      Set.range (entry b₀) = pool n ∧ Function.Injective (entry b₀) ∧
      ∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∃ out : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum out r : ℤ) - (rowSum b₀ r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer source target fr e r) ∧
        (∀ c, (columnSum out c : ℤ) - (columnSum b₀ c : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer source target fc e c) ∧
        mainSum out = mainSum b₀ ∧ antiSum out = antiSum b₀ ∧
        (∀ c ∈ rect, entry out c = entry b₀ c) ∧
        (∀ c ∉ active, entry out c = entry b c) ∧
        active.image (entry out) = active.image (entry b) ∧
        Set.range (entry out) = pool n ∧ Function.Injective (entry out) := by
  dsimp only
  let active := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hr hc sr sc hsr hsc wr wc hwr hwc ∪
    Finset.univ.image (btGrowingOffsetCells
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
  have hactive := fw_role_cells_eq_active_support hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hr hc hsr hsc hwr hwc hgr hgc
  have hrowActive : LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ⊆ active := by
    rw [show active = _ from hactive]
    intro c hc
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hc)
  have hcolActive : LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc)) ⊆ active := by
    rw [show active = _ from hactive]
    intro c hc
    exact Finset.mem_union_right _ hc
  obtain ⟨b₀, hinvoice, hm, ha, hfixed', houtside, himage, hpool, hinj, hflows⟩ :=
    twoNetworks_centered_invoice_preserves_active_values b rect active
      (((br ++ sr) ++ wr) ++ gr) (((bc ++ sc) ++ wc) ++ gc) hrows hcols hrowActive hcolActive
      (fwPhysicalRowLayerGap b _) (fwPhysicalColumnLayerGap b _) hrowGap hcolGap BR BC
  have hmids := fw_reallocated_reference_physical_midpoints p batches hvalid hrect hseed hwide hs choice
    br bc hr hc sr sc hsr hsc wr wc hwr hwc old grown b b₀ hfixed hplace hbridge hwidePreserved hseedNew
    trace (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff gr gc hgr hgc
    hgrowthPreserved hgrowthOld wide hwideOld rect hrows hcols hrowGap hcolGap BR BC
    hends hblockR hblockC hradius hsame hinvoice
  have hRs : BR.source = (fun e : Fin 3 × Fin n => e.2) := by
    funext e; exact (hends e).1
  have hCs : BC.source = (fun e : Fin 3 × Fin n => e.2) := by
    funext e; exact (hends e).2.1
  have hRt : BR.target = (fun e : Fin 3 × Fin n => p e.1 e.2) := by
    funext e; exact (hends e).2.2.1
  have hCt : BC.target = (fun e : Fin 3 × Fin n => p e.1 e.2) := by
    funext e; exact (hends e).2.2.2
  refine ⟨b₀, hinvoice, hmids.1, hmids.2, hm, ha, hfixed', houtside, himage, hpool, hinj, ?_⟩
  intro fr hfr fc hfc
  obtain ⟨hre, hrl, hrh⟩ := scaled_flow_within_center BR.radius N fr hR hfr
  obtain ⟨hce, hcl, hch⟩ := scaled_flow_within_center BC.radius N fc hC hfc
  obtain ⟨out, hrows', hcols', hm', ha', hfixed'', houtside', himage', hpool', hinj'⟩ :=
    hflows (fun e => 2 * fr e) hre hrl hrh (fun e => 2 * fc e) hce hcl hch
  refine ⟨out, ?_, ?_, hm', ha', hfixed'', houtside', himage', hpool', hinj'⟩
  · intro r
    exact (hrows' r).trans (edgeTransfer_sum_scale_two BR.source BR.target fr r) |>.trans (by rw [hRs, hRt])
  · intro c
    exact (hcols' c).trans (edgeTransfer_sum_scale_two BC.source BC.target fc c) |>.trans (by rw [hCs, hCt])

end
end Sude
