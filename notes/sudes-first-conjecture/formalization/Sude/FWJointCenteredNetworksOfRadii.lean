import Sude.FWJointCenteredNetwork
import Sude.FWJointGraphEndpoints

/-! Centered networks on the same supplied joint layers, with arbitrary
per-edge radii and a supplied common capacity. No bound or flow is proved. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

/-- Same-square physical grids on the actual joint slots form centered row
and transposed-column networks with the same per-edge radii and graph. -/
theorem fw_joint_centered_networks_of_radii {n P : ℕ}
    (a : Cell n ≃ Fin (n*n)) (rect : Finset (Cell n))
    (p : Fin 3 → Equiv.Perm (Fin n))
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hbrow : br.map Prod.fst = bridgeRepeatedPermutations 5 p)
    (hbcol : bc.map Prod.fst = bridgeRepeatedPermutations 5 p)
    (hsrow : sr.map Prod.fst = bridgeRepeatedPermutations 16 p)
    (hscol : sc.map Prod.fst = bridgeRepeatedPermutations 16 p)
    (hwrow : wr.map Prod.fst = bridgeRepeatedPermutations (3 * (n / 450)) p)
    (hwcol : wc.map Prod.fst = bridgeRepeatedPermutations (3 * (n / 450)) p)
    (hgrow : gr.map Prod.fst = bridgeRepeatedPermutations P p)
    (hgcol : gc.map Prod.fst = bridgeRepeatedPermutations P p)
    (hrows : LayerPacking.PackedLayers rect (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc))
    (hrowGap : ∀ i e, entry a (((((br ++ sr) ++ wr) ++ gr).get i).1 e,
        ((((br ++ sr) ++ wr) ++ gr).get i).2 e) =
      entry a (e, ((((br ++ sr) ++ wr) ++ gr).get i).2 e) +
        fwPhysicalRowLayerGap a (((br ++ sr) ++ wr) ++ gr) i e)
    (hcolGap : ∀ i e, entry a (((((bc ++ sc) ++ wc) ++ gc).get i).2 e,
        ((((bc ++ sc) ++ wc) ++ gc).get i).1 e) =
      entry a (((((bc ++ sc) ++ wc) ++ gc).get i).2 e, e) +
        fwPhysicalColumnLayerGap a (((bc ++ sc) ++ wc) ++ gc) i e)
    (R : Fin 3 × Fin n → ℕ) (capacity : ℕ) (hcapacity : ∀ edge, capacity ≤ R edge)
    (hgrids : ∀ edge : Fin 3 × Fin n,
      let labels := fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))
      let rowSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)
      let colSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)
      CompleteEvenGrid (labels.attach.image rowSlot) (fun x => fwPhysicalRowLayerGap a (((br ++ sr) ++ wr) ++ gr) x.1 x.2) (R edge) ∧
      CompleteEvenGrid (labels.attach.image colSlot) (fun x => fwPhysicalColumnLayerGap a (((bc ++ sc) ++ wc) ++ gc) x.1 x.2) (R edge)) :
    let rows := ((br ++ sr) ++ wr) ++ gr
    let cols := ((bc ++ sc) ++ wc) ++ gc
    let vrow := hrows.rowPairs a (fwPhysicalRowLayerGap a rows) hrowGap
    let vcol := hcols.columnPairs a (fwPhysicalColumnLayerGap a cols) hcolGap
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
      (∀ edge, BR.radius edge = R edge ∧ BC.radius edge = R edge ∧ capacity ≤ BR.radius edge) := by
  classical
  dsimp only at hgrids ⊢
  let labels := fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))
  let rows := ((br ++ sr) ++ wr) ++ gr
  let cols := ((bc ++ sc) ++ wc) ++ gc
  let rslot := fun xe : {x // x ∈ labels} × (Fin 3 × Fin n) =>
    fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((xe.1,xe.2.1),xe.2.2)
  let cslot := fun xe : {x // x ∈ labels} × (Fin 3 × Fin n) =>
    fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((xe.1,xe.2.1),xe.2.2)
  have hri : Function.Injective rslot := by
    rintro ⟨x,⟨k,e⟩⟩ ⟨y,⟨k',e'⟩⟩ heq
    have h := fwJointActualGridPairIndex_injective br sr wr gr hr hsr hwr hgr heq
    cases h; rfl
  have hci : Function.Injective cslot := by
    rintro ⟨x,⟨k,e⟩⟩ ⟨y,⟨k',e'⟩⟩ heq
    have h := fwJointActualGridPairIndex_injective bc sc wc gc hc hsc hwc hgc heq
    cases h; rfl
  let vr := hrows.rowPairs a (fwPhysicalRowLayerGap a rows) hrowGap
  let vc := hcols.columnPairs a (fwPhysicalColumnLayerGap a cols) hcolGap
  have hrg (edge : Fin 3 × Fin n) : CompleteEvenGrid (labels.attach.image (fun x => rslot (x,edge))) vr.gap (R edge) :=
    (hgrids edge).1
  have hcg (edge : Fin 3 × Fin n) : CompleteEvenGrid (labels.attach.image (fun x => cslot (x,edge))) vc.gap (R edge) :=
    (hgrids edge).2
  have hre (edge : Fin 3 × Fin n) (x : {x // x ∈ labels}) :
      vr.low (rslot (x,edge)) = edge.2 ∧ vr.high (rslot (x,edge)) = p edge.1 edge.2 := by
    have h := fw_joint_actual_grid_pair_graph_of_maps br sr wr gr hr hsr hwr hgr p
      hbrow hsrow hwrow hgrow x edge
    exact ⟨h.1, h.2⟩
  have hce (edge : Fin 3 × Fin n) (x : {x // x ∈ labels}) :
      vc.low (cslot (x,edge)) = edge.2 ∧ vc.high (cslot (x,edge)) = p edge.1 edge.2 := by
    have h := fw_joint_actual_grid_pair_graph_of_maps bc sc wc gc hc hsc hwc hgc p
      hbcol hscol hwcol hgcol x edge
    exact ⟨h.1, h.2⟩
  let BR := centeredNetwork_of_supported_grids vr labels rslot hri R Prod.snd (fun edge => p edge.1 edge.2) hrg hre
  let BC := centeredNetwork_of_supported_grids vc labels cslot hci R Prod.snd (fun edge => p edge.1 edge.2) hcg hce
  refine ⟨BR, BC, ?_, ?_, ?_, ?_⟩
  · intro edge; exact ⟨rfl, rfl, rfl, rfl⟩
  · intro edge; rfl
  · intro edge; rfl
  · intro edge; exact ⟨rfl, rfl, hcapacity edge⟩

end
end Sude
