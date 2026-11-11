import Sude.FWJointCenteredNetwork
import Sude.FWActualEdgeGridTransport

/-! Assemble explicitly supplied same-witness wide gaps and joint edge grids into actual centered
row and column networks. No demand routing or line repair is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

/-- The actual joint pair sets and their shared wide gaps form two centered
networks on the same graph. The numeric capacity comes from the wide sum. -/
theorem fw_actual_joint_centered_networks_explicit_wide {n P : ℕ}
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
    let rows := ((br ++ sr) ++ wr) ++ gr
    let cols := ((bc ++ sc) ++ wc) ++ gc
    let vrow := hrows.rowPairs grown (fwPhysicalRowLayerGap grown rows) hrowGap
    let vcol := hcols.columnPairs grown (fwPhysicalColumnLayerGap grown cols) hcolGap
    ∃ (BR : CenteredNetwork (Fin 3 × Fin n) (Fin rows.length × Fin n) vrow)
      (BC : CenteredNetwork (Fin 3 × Fin n) (Fin cols.length × Fin n) vcol),
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
      (∀ edge, 2 * ((n / 450) * poolMaximum n) ≤ BR.radius edge) := by
  classical
  dsimp only at hgrids ⊢
  let labels := fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))
  let rows := ((br ++ sr) ++ wr) ++ gr
  let cols := ((bc ++ sc) ++ wc) ++ gc
  have hw (edge : Fin 3 × Fin n) := hgrids edge
  let R := fun edge : Fin 3 × Fin n => last +
    (∑ j ∈ Finset.range 5, selectedBridgeGap batches
      (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge) j) + ∑ j, wide edge j
  let rslot := fun xe : {x // x ∈ labels} × (Fin 3 × Fin n) =>
    fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((xe.1,xe.2.1),xe.2.2)
  let cslot := fun xe : {x // x ∈ labels} × (Fin 3 × Fin n) =>
    fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((xe.1,xe.2.1),xe.2.2)
  have hri : Function.Injective rslot := by
    rintro ⟨x,⟨k,e⟩⟩ ⟨y,⟨k',e'⟩⟩ heq
    have h := fwJointActualGridPairIndex_injective br sr wr gr hr hsr hwr hgr heq
    cases h
    rfl
  have hci : Function.Injective cslot := by
    rintro ⟨x,⟨k,e⟩⟩ ⟨y,⟨k',e'⟩⟩ heq
    have h := fwJointActualGridPairIndex_injective bc sc wc gc hc hsc hwc hgc heq
    cases h
    rfl
  let vr := hrows.rowPairs grown (fwPhysicalRowLayerGap grown rows) hrowGap
  let vc := hcols.columnPairs grown (fwPhysicalColumnLayerGap grown cols) hcolGap
  have hrg (edge : Fin 3 × Fin n) : CompleteEvenGrid (labels.attach.image (fun x => rslot (x,edge))) vr.gap (R edge) := by
    exact (hw edge).1
  have hcg (edge : Fin 3 × Fin n) : CompleteEvenGrid (labels.attach.image (fun x => cslot (x,edge))) vc.gap (R edge) := by
    exact (hw edge).2.1
  have hre (edge : Fin 3 × Fin n) (x : {x // x ∈ labels}) :
      vr.low (rslot (x,edge)) = edge.2 ∧ vr.high (rslot (x,edge)) = p edge.1 edge.2 := by
    have h := congrArg Prod.fst ((hw edge).2.2.1 x true)
    constructor
    · rfl
    · simpa [vr, LayerPacking.PackedLayers.rowPairs, rslot,
        LayerPacking.sequenceCell, LayerPacking.layerCell] using h
  have hce (edge : Fin 3 × Fin n) (x : {x // x ∈ labels}) :
      vc.low (cslot (x,edge)) = edge.2 ∧ vc.high (cslot (x,edge)) = p edge.1 edge.2 := by
    have h := congrArg Prod.snd ((hw edge).2.2.2.1 x true)
    constructor
    · rfl
    · simpa [vc, LayerPacking.PackedLayers.columnPairs, LayerPacking.PackedLayers.rowPairs, cslot,
        LayerPacking.transposePlacement, LayerPacking.sequenceCell, LayerPacking.layerCell] using h
  let BR := centeredNetwork_of_supported_grids vr labels rslot hri R Prod.snd (fun edge => p edge.1 edge.2) hrg hre
  let BC := centeredNetwork_of_supported_grids vc labels cslot hci R Prod.snd (fun edge => p edge.1 edge.2) hcg hce
  refine ⟨BR, BC, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro edge; exact ⟨rfl, rfl, rfl, rfl⟩
  · intro edge; rfl
  · intro edge; rfl
  · intro edge; rfl
  · intro edge; rfl
  · intro edge
    have hs := (hw edge).2.2.2.2
    have hreal : (2 : ℝ) * ((n / 450 : ℕ) : ℝ) * (poolMaximum n : ℝ) ≤ (R edge : ℝ) := by
      dsimp [R]
      push_cast
      have hn1 : (0 : ℝ) ≤ last := by positivity
      have hn2 : (0 : ℝ) ≤ ∑ j ∈ Finset.range 5, (selectedBridgeGap batches
        (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge) j : ℝ) := by positivity
      linarith
    change 2 * ((n / 450) * poolMaximum n) ≤ R edge
    have hn : 2 * (n / 450) * poolMaximum n ≤ R edge := by exact_mod_cast hreal
    simpa [Nat.mul_assoc] using hn

end
end Sude
