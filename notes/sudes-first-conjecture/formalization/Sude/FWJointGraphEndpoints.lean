import Sude.FWJointSupportedIndex
import Sude.FWWideEdgeRoles

/-! Identify each supported joint pair with its supplied graph edge. The
family layer endpoint equalities or repeated-permutation maps are inputs;
no grid, physical gap, switching or flow result is asserted here. -/
namespace Sude
noncomputable section
set_option maxRecDepth 8192

/-- Recover the wide layer endpoints from the coordinate equations exported by
the physical crossing witness. Only the high side of each pair is needed. -/
theorem fw_wide_layer_endpoints_of_physical_coordinates {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (wr wc : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (p : Fin 3 → Equiv.Perm (Fin n))
    (hcoords : ∀ (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n) (side : Bool),
      fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e false side) =
        ((if side then p k e else e), (wr.get (bridgeStageLayerIndex hwr j k)).2 e) ∧
      fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e true side) =
        ((wc.get (bridgeStageLayerIndex hwc j k)).2 e, (if side then p k e else e))) :
    ∀ (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n),
      (wr.get (bridgeStageLayerIndex hwr j k)).1 e = p k e ∧
      (wc.get (bridgeStageLayerIndex hwc j k)).1 e = p k e := by
  intro j k e
  have hr := congrArg Prod.fst (hcoords j k e true).1
  have hc := congrArg Prod.snd (hcoords j k e true).2
  constructor
  · simpa [fwWidePhysicalCells, fwWideEdgeRole, fwWideOrdinaryCells, fwWideLayerIndex,
      bridgeStageLayerIndex, LayerPacking.sequenceCell, LayerPacking.layerCell] using hr
  · simpa [fwWidePhysicalCells, fwWideEdgeRole, fwWideOrdinaryCells, fwWideLayerIndex,
      bridgeStageLayerIndex, LayerPacking.sequenceCell, LayerPacking.layerCell] using hc

/-- Every supported family label retrieves a layer with the supplied graph
endpoint; the four family lengths and endpoint identities remain explicit. -/
theorem fw_joint_supported_layer_graph {n P : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (p : Fin 3 → Equiv.Perm (Fin n))
    (hb : ∀ (j : Fin 5) (k : Fin 3) (e : Fin n),
      (br.get (bridgeStageLayerIndex hbr j k)).1 e = p k e)
    (hs : ∀ (j : Fin 16) (k : Fin 3) (e : Fin n),
      (sr.get (bridgeStageLayerIndex hsr j k)).1 e = p k e)
    (hw : ∀ (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n),
      (wr.get (bridgeStageLayerIndex hwr j k)).1 e = p k e)
    (hg : ∀ (j : Fin P) (k : Fin 3) (e : Fin n),
      (gr.get (bridgeStageLayerIndex hgr j k)).1 e = p k e)
    (tag : FWJointSupportedTag n P) (k : Fin 3) (e : Fin n) :
    ((((br ++ sr) ++ wr) ++ gr).get
      (fwJointSupportedLayerIndex br sr wr gr hbr hsr hwr hgr tag k)).1 e = p k e := by
  cases tag with
  | seed j =>
    simp only [fwJointSupportedLayerIndex, fwSeedJointLayerIndex_get]
    exact hs j k e
  | growth j =>
    simp only [fwJointSupportedLayerIndex, fwGrowthJointLayerIndex_get]
    exact hg j k e
  | bridge j =>
    simp only [fwJointSupportedLayerIndex, fwBridgeJointLayerIndex_get]
    exact hb (fwBridgeSupportStage j) k e
  | wide j =>
    simp only [fwJointSupportedLayerIndex, fwWideJointLayerIndex_get]
    exact hw j k e

/-- The actual nested grid-support index retains the vertex and the same
graph endpoint for all four family tags. -/
theorem fw_joint_actual_grid_pair_graph {n P : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (p : Fin 3 → Equiv.Perm (Fin n))
    (hb : ∀ (j : Fin 5) (k : Fin 3) (e : Fin n),
      (br.get (bridgeStageLayerIndex hbr j k)).1 e = p k e)
    (hs : ∀ (j : Fin 16) (k : Fin 3) (e : Fin n),
      (sr.get (bridgeStageLayerIndex hsr j k)).1 e = p k e)
    (hw : ∀ (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n),
      (wr.get (bridgeStageLayerIndex hwr j k)).1 e = p k e)
    (hg : ∀ (j : Fin P) (k : Fin 3) (e : Fin n),
      (gr.get (bridgeStageLayerIndex hgr j k)).1 e = p k e)
    (tag : {t // t ∈ fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))})
    (edge : Fin 3 × Fin n) :
    let x := fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((tag, edge.1), edge.2)
    x.2 = edge.2 ∧ ((((br ++ sr) ++ wr) ++ gr).get x.1).1 edge.2 = p edge.1 edge.2 := by
  constructor
  · rfl
  · exact fw_joint_supported_layer_graph br sr wr gr hbr hsr hwr hgr p hb hs hw hg
      (fwJointSupportedTagOfGrid ⟨tag.val, fwJointGridLabels_supported tag.val tag.property⟩)
      edge.1 edge.2

/-- Repeated stage-wise permutation maps are sufficient for the four family
endpoint hypotheses of the supported-label result. -/
theorem fw_joint_actual_grid_pair_graph_of_maps {n P : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (p : Fin 3 → Equiv.Perm (Fin n))
    (hb : br.map Prod.fst = bridgeRepeatedPermutations 5 p)
    (hs : sr.map Prod.fst = bridgeRepeatedPermutations 16 p)
    (hw : wr.map Prod.fst = bridgeRepeatedPermutations (3 * (n / 450)) p)
    (hg : gr.map Prod.fst = bridgeRepeatedPermutations P p)
    (tag : {t // t ∈ fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))})
    (edge : Fin 3 × Fin n) :
    let x := fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((tag, edge.1), edge.2)
    x.2 = edge.2 ∧ ((((br ++ sr) ++ wr) ++ gr).get x.1).1 edge.2 = p edge.1 edge.2 := by
  exact fw_joint_actual_grid_pair_graph br sr wr gr hbr hsr hwr hgr p
    (bridgeStageLayer_endpoints br hbr p hb) (bridgeStageLayer_endpoints sr hsr p hs)
    (bridgeStageLayer_endpoints wr hwr p hw) (bridgeStageLayer_endpoints gr hgr p hg) tag edge

/-- Apply the endpoint-input interface to both row and transposed-column
families on the same graph and supported tag. -/
theorem fw_joint_actual_grid_row_column_graph {n P : ℕ}
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (p : Fin 3 → Equiv.Perm (Fin n))
    (hb : ∀ (j : Fin 5) (k : Fin 3) (e : Fin n),
      (br.get (bridgeStageLayerIndex hbr j k)).1 e = p k e ∧
      (bc.get (bridgeStageLayerIndex hbc j k)).1 e = p k e)
    (hs : ∀ (j : Fin 16) (k : Fin 3) (e : Fin n),
      (sr.get (bridgeStageLayerIndex hsr j k)).1 e = p k e ∧
      (sc.get (bridgeStageLayerIndex hsc j k)).1 e = p k e)
    (hw : ∀ (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n),
      (wr.get (bridgeStageLayerIndex hwr j k)).1 e = p k e ∧
      (wc.get (bridgeStageLayerIndex hwc j k)).1 e = p k e)
    (hg : ∀ (j : Fin P) (k : Fin 3) (e : Fin n),
      (gr.get (bridgeStageLayerIndex hgr j k)).1 e = p k e ∧
      (gc.get (bridgeStageLayerIndex hgc j k)).1 e = p k e)
    (tag : {t // t ∈ fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))})
    (edge : Fin 3 × Fin n) :
    let r := fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((tag, edge.1), edge.2)
    let c := fwJointActualGridPairIndex bc sc wc gc hbc hsc hwc hgc ((tag, edge.1), edge.2)
    (r.2 = edge.2 ∧ ((((br ++ sr) ++ wr) ++ gr).get r.1).1 edge.2 = p edge.1 edge.2) ∧
    (c.2 = edge.2 ∧ ((((bc ++ sc) ++ wc) ++ gc).get c.1).1 edge.2 = p edge.1 edge.2) := by
  constructor
  · exact fw_joint_actual_grid_pair_graph br sr wr gr hbr hsr hwr hgr p
      (fun j k e => (hb j k e).1) (fun j k e => (hs j k e).1)
      (fun j k e => (hw j k e).1) (fun j k e => (hg j k e).1) tag edge
  · exact fw_joint_actual_grid_pair_graph bc sc wc gc hbc hsc hwc hgc p
      (fun j k e => (hb j k e).2) (fun j k e => (hs j k e).2)
      (fun j k e => (hw j k e).2) (fun j k e => (hg j k e).2) tag edge

end
end Sude
