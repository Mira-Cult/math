import Sude.FWActualExplicitWideNetworks
import Sude.FWCenteredFlowInvoice

/-! Retain the actual physical networks and their centering invoice for the
same reference realizing supplied flows. No line or target bound is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

/-- The supplied-wide joint grids, common reference invoice and supplied-flow
realization all refer to the same actual row and column networks. -/
theorem fw_actual_grids_realize_supplied_flows_with_explicit_wide_invoice {n P : ℕ}
    (grown : Cell n ≃ Fin (n*n)) (rect : Finset (Cell n))
    (p : Fin 3 → Equiv.Perm (Fin n)) (batches : ℕ → List DoublePair) (last : ℕ)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers rect (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc))
    (hrowGap : ∀ i e, entry grown (((((br ++ sr) ++ wr) ++ gr).get i).1 e,
        ((((br ++ sr) ++ wr) ++ gr).get i).2 e) =
      entry grown (e, ((((br ++ sr) ++ wr) ++ gr).get i).2 e) +
        fwPhysicalRowLayerGap grown (((br ++ sr) ++ wr) ++ gr) i e)
    (hcolGap : ∀ i e, entry grown (((((bc ++ sc) ++ wc) ++ gc).get i).2 e,
        ((((bc ++ sc) ++ wc) ++ gc).get i).1 e) =
      entry grown (((((bc ++ sc) ++ wc) ++ gc).get i).2 e, e) +
        fwPhysicalColumnLayerGap grown (((bc ++ sc) ++ wc) ++ gc) i e)
    (wide : (Fin 3 × Fin n) → Fin (3 * (n / 450)) → ℕ)
    (hgrids : ∀ edge : Fin 3 × Fin n,
      let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
      let radius := last + ∑ j ∈ Finset.range 5, selectedBridgeGap batches index j
      let labels := fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))
      let rows := ((br ++ sr) ++ wr) ++ gr
      let cols := ((bc ++ sc) ++ wc) ++ gc
      let rowSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)
      let colSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)
      CompleteEvenGrid (labels.attach.image rowSlot) (fun x => fwPhysicalRowLayerGap grown rows x.1 x.2)
          (radius + ∑ j, wide edge j) ∧
        CompleteEvenGrid (labels.attach.image colSlot) (fun x => fwPhysicalColumnLayerGap grown cols x.1 x.2)
          (radius + ∑ j, wide edge j) ∧
        (∀ x side, LayerPacking.sequenceCell rows ((rowSlot x).1, ((rowSlot x).2, side)) =
          ((if side then p edge.1 edge.2 else edge.2), (rows.get (rowSlot x).1).2 edge.2)) ∧
        (∀ x side, (LayerPacking.sequenceCell cols ((colSlot x).1, ((colSlot x).2, side))).swap =
          ((cols.get (colSlot x).1).2 edge.2, (if side then p edge.1 edge.2 else edge.2))) ∧
        (2 : ℝ) * (n / 450 : ℕ) * (poolMaximum n : ℝ) ≤ ∑ j, (wide edge j : ℝ)) :
    let N := (n / 450) * poolMaximum n
    let source : Fin 3 × Fin n → Fin n := fun e => e.2
    let target : Fin 3 × Fin n → Fin n := fun e => p e.1 e.2
    let rowLayers := ((br ++ sr) ++ wr) ++ gr
    let colLayers := ((bc ++ sc) ++ wc) ++ gc
    let rowGap := fwPhysicalRowLayerGap grown rowLayers
    let colGap := fwPhysicalColumnLayerGap grown colLayers
    ∃ (BR : CenteredNetwork (Fin 3 × Fin n) (Fin rowLayers.length × Fin n)
        (hrows.rowPairs grown rowGap hrowGap))
      (BC : CenteredNetwork (Fin 3 × Fin n) (Fin colLayers.length × Fin n)
        (hcols.columnPairs grown colGap hcolGap))
      (b₀ : Cell n ≃ Fin (n*n)),
      TwoNetworkReferenceInvoice grown b₀ rowLayers colLayers hrows hcols rowGap colGap
        hrowGap hcolGap BR BC ∧
      (∀ edge, BR.source edge = edge.2 ∧ BC.source edge = edge.2 ∧
        BR.target edge = p edge.1 edge.2 ∧ BC.target edge = p edge.1 edge.2) ∧
      (∀ edge, BR.block edge =
        (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
          (fun x => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2))) ∧
      (∀ edge, BC.block edge =
        (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
          (fun x => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2))) ∧
      (∀ edge, BR.radius edge = last +
        (∑ j ∈ Finset.range 5, selectedBridgeGap batches
          (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge) j) + ∑ j, wide edge j) ∧
      (∀ edge, BC.radius edge = BR.radius edge) ∧
      (∀ edge, 2 * N ≤ BR.radius edge) ∧
      mainSum b₀ = mainSum grown ∧ antiSum b₀ = antiSum grown ∧
      (∀ c ∈ rect, entry b₀ c = entry grown c) ∧
      ∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∃ b : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer source target fr e r) ∧
        (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer source target fc e c) ∧
        mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
        (∀ c ∈ rect, entry b c = entry b₀ c) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  dsimp only
  obtain ⟨BR, BC, hends, hblocksR, hblocksC, hradius, hsame, hcapacity⟩ :=
    fw_actual_joint_centered_networks_explicit_wide grown rect p batches last br bc sr sc wr wc gr gc
      hr hc hsr hsc hwr hwc hgr hgc hrows hcols hrowGap hcolGap wide hgrids
  have hRs : BR.source = fun e : Fin 3 × Fin n => e.2 := by
    funext e
    exact (hends e).1
  have hCs : BC.source = fun e : Fin 3 × Fin n => e.2 := by
    funext e
    exact (hends e).2.1
  have hRt : BR.target = fun e : Fin 3 × Fin n => p e.1 e.2 := by
    funext e
    exact (hends e).2.2.1
  have hCt : BC.target = fun e : Fin 3 × Fin n => p e.1 e.2 := by
    funext e
    exact (hends e).2.2.2
  have hC : ∀ e, 2 * ((n / 450) * poolMaximum n) ≤ BC.radius e := by
    intro e
    rw [hsame e]
    exact hcapacity e
  obtain ⟨b₀, hinvoice, hm, ha, hfixed, hflows⟩ :=
    fw_centered_networks_realize_supplied_flows_with_invoice p grown rect
      (((br ++ sr) ++ wr) ++ gr) (((bc ++ sc) ++ wc) ++ gc) hrows hcols
      (fwPhysicalRowLayerGap grown _) (fwPhysicalColumnLayerGap grown _) hrowGap hcolGap
      BR BC hRs hRt hCs hCt hcapacity hC
  exact ⟨BR, BC, b₀, hinvoice, hends, hblocksR, hblocksC, hradius, hsame,
    hcapacity, hm, ha, hfixed, hflows⟩

end
end Sude
