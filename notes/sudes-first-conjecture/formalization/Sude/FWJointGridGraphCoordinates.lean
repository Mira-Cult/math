import Sude.FWJointGraphEndpoints

/-! Coordinates of actual supported grid slots on a common graph. This
requires the supplied family layer maps; it makes no assertion of pair-value
orientation, packed support, flow, or the existence of a grid. -/
namespace Sude
noncomputable section
set_option maxRecDepth 8192

/-- Every supported joint row slot and transposed column slot follows the
same directed graph edge. The labels and physical slots are unchanged. -/
theorem fw_joint_grid_graph_coordinates_of_maps {n P : ℕ}
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (p : Fin 3 → Equiv.Perm (Fin n))
    (hbrow : br.map Prod.fst = bridgeRepeatedPermutations 5 p)
    (hbcol : bc.map Prod.fst = bridgeRepeatedPermutations 5 p)
    (hsrow : sr.map Prod.fst = bridgeRepeatedPermutations 16 p)
    (hscol : sc.map Prod.fst = bridgeRepeatedPermutations 16 p)
    (hwrow : wr.map Prod.fst = bridgeRepeatedPermutations (3 * (n / 450)) p)
    (hwcol : wc.map Prod.fst = bridgeRepeatedPermutations (3 * (n / 450)) p)
    (hgrow : gr.map Prod.fst = bridgeRepeatedPermutations P p)
    (hgcol : gc.map Prod.fst = bridgeRepeatedPermutations P p)
    (edge : Fin 3 × Fin n) :
    let labels := fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))
    let rows := ((br ++ sr) ++ wr) ++ gr
    let cols := ((bc ++ sc) ++ wc) ++ gc
    let rowSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2)
    let colSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex bc sc wc gc hbc hsc hwc hgc ((x,edge.1),edge.2)
    (∀ x side, layerPairSlot rows (rowSlot x) side =
      ((if side then p edge.1 edge.2 else edge.2), (rows.get (rowSlot x).1).2 edge.2)) ∧
    (∀ x side, (layerPairSlot cols (colSlot x) side).swap =
      ((cols.get (colSlot x).1).2 edge.2, (if side then p edge.1 edge.2 else edge.2))) := by
  dsimp only
  constructor
  · intro x side
    obtain ⟨he, hp⟩ := fw_joint_actual_grid_pair_graph_of_maps br sr wr gr hbr hsr hwr hgr p
      hbrow hsrow hwrow hgrow x edge
    cases side <;> simp [layerPairSlot, LayerPacking.sequenceCell, LayerPacking.layerCell, he]
    simpa using hp
  · intro x side
    obtain ⟨he, hp⟩ := fw_joint_actual_grid_pair_graph_of_maps bc sc wc gc hbc hsc hwc hgc p
      hbcol hscol hwcol hgcol x edge
    cases side <;> simp [layerPairSlot, LayerPacking.sequenceCell, LayerPacking.layerCell, he]
    simpa using hp

end
end Sude
