import Sude.FWJointSupportedIndex
import Sude.NetworkSwitches

/-! Global supported-index separation of actual row and column switch cells.
No selection of switches or flow is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 8192

/-- Injective pair labels in normalized packed row/column networks give
injective endpoint maps, disjoint orientations, and reservation avoidance. -/
theorem fw_packed_network_supported_cells_separate {n : ℕ} {α : Type*}
    (rect : Finset (Cell n)) (rows cols : List (LayerPacking.Layer n))
    (hrows : LayerPacking.PackedLayers rect rows)
    (hcols : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (rect ∪ LayerPacking.layersSupport rows)) cols)
    (rslot : α → Fin rows.length × Fin n) (cslot : α → Fin cols.length × Fin n)
    (hrinj : Function.Injective rslot) (hcinj : Function.Injective cslot) :
    Function.Injective (fun x : α × Bool => layerPairSlot rows (rslot x.1) x.2) ∧
    Function.Injective (fun x : α × Bool => (layerPairSlot cols (cslot x.1) x.2).swap) ∧
    (∀ x y : α × Bool, layerPairSlot rows (rslot x.1) x.2 ≠
      (layerPairSlot cols (cslot y.1) y.2).swap) ∧
    (∀ x : α × Bool, layerPairSlot rows (rslot x.1) x.2 ∉ rect) ∧
    (∀ x : α × Bool, (layerPairSlot cols (cslot x.1) x.2).swap ∉ rect) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨x, s⟩ ⟨y, t⟩ heq
    have h := hrows.sequenceCell_injective heq
    have hslot : rslot x = rslot y := Prod.ext
      (congrArg (fun z : Fin rows.length × (Fin n × Bool) => z.1) h)
      (congrArg (fun z : Fin rows.length × (Fin n × Bool) => z.2.1) h)
    have hxy := hrinj hslot
    have hst := congrArg (fun z => z.2.2) h
    cases hxy
    cases hst
    rfl
  · rintro ⟨x, s⟩ ⟨y, t⟩ heq
    have heq' := congrArg Prod.swap heq
    simp only [Prod.swap_swap] at heq'
    have h := hcols.sequenceCell_injective heq'
    have hslot : cslot x = cslot y := Prod.ext
      (congrArg (fun z : Fin cols.length × (Fin n × Bool) => z.1) h)
      (congrArg (fun z : Fin cols.length × (Fin n × Bool) => z.2.1) h)
    have hxy := hcinj hslot
    have hst := congrArg (fun z => z.2.2) h
    cases hxy
    cases hst
    rfl
  · intro x y heq
    have hrow := layerPairSlot_mem rows (rslot x.1) x.2
    have hcol := transposedLayerPairSlot_mem cols (cslot y.1) y.2
    have hsafe := (hcols.transposed_support_safe _ hcol).1
    apply hsafe
    exact Finset.mem_union_right rect (heq ▸ hrow)
  · intro x
    exact hrows.sequenceCell_unreserved ((rslot x.1).1, ((rslot x.1).2, x.2))
  · intro x
    have hsafe := (hcols.transposed_support_safe _ (transposedLayerPairSlot_mem cols (cslot x.1) x.2)).1
    intro hm
    exact hsafe (Finset.mem_union_left _ hm)

/-- The actual supported seed/growth/bridge/wide labels, graph edges and
endpoint sides name globally distinct cells in each network; the two networks
and the rectangle reservation are physically disjoint. -/
theorem fw_joint_actual_supported_cells_separate {n P : ℕ}
    (rect : Finset (Cell n)) (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers rect (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc)) :
    let α := ({t // t ∈ fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))} × Fin 3) × Fin n
    let rslot : α → Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n :=
      fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr
    let cslot : α → Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n :=
      fwJointActualGridPairIndex bc sc wc gc hbc hsc hwc hgc
    Function.Injective (fun x : α × Bool => layerPairSlot (((br ++ sr) ++ wr) ++ gr) (rslot x.1) x.2) ∧
    Function.Injective (fun x : α × Bool => (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (cslot x.1) x.2).swap) ∧
    (∀ x y : α × Bool, layerPairSlot (((br ++ sr) ++ wr) ++ gr) (rslot x.1) x.2 ≠
      (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (cslot y.1) y.2).swap) ∧
    (∀ x : α × Bool, layerPairSlot (((br ++ sr) ++ wr) ++ gr) (rslot x.1) x.2 ∉ rect) ∧
    (∀ x : α × Bool, (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (cslot x.1) x.2).swap ∉ rect) := by
  exact fw_packed_network_supported_cells_separate rect _ _ hrows hcols _ _
    (fwJointActualGridPairIndex_injective br sr wr gr hbr hsr hwr hgr)
    (fwJointActualGridPairIndex_injective bc sc wc gc hbc hsc hwc hgc)

end
end Sude
