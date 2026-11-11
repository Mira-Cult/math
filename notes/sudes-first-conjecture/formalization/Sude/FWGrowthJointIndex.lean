import Sude.FWJointPhysicalGaps
import Sude.FWPhysicalEdgeWitnessGrid

/-! Map trace-stage labels to growth layers in the joint physical networks.
This does not transport a grid, choose switches, or construct flow. -/
namespace Sude
noncomputable section
set_option maxRecDepth 8192

/-- The growth stage/layer index in the combined bridge/seed/wide/growth list. -/
def fwGrowthJointLayerIndex {n P : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hgr : gr.length = P * 3) (j : Fin P) (k : Fin 3) :
    Fin (((br ++ sr) ++ wr) ++ gr).length :=
  ⟨br.length + sr.length + wr.length + (finProdFinEquiv (j, k)).val, by
    simp only [List.length_append]
    have hi := (finProdFinEquiv (j, k)).isLt
    omega⟩

/-- The joint growth index retrieves the original physical growth layer. -/
theorem fwGrowthJointLayerIndex_get {n P : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hgr : gr.length = P * 3) (j : Fin P) (k : Fin 3) :
    (((br ++ sr) ++ wr) ++ gr).get (fwGrowthJointLayerIndex br sr wr gr hgr j k) =
      gr.get (bridgeStageLayerIndex hgr j k) := by
  simp only [List.get_eq_getElem]
  unfold fwGrowthJointLayerIndex bridgeStageLayerIndex
  simp only [Fin.val_cast]
  rw [List.getElem_append_right (by simp only [List.length_append]; omega)]
  congr 1
  simp only [List.length_append]
  omega

/-- The joint pair labels recover growth stage, graph layer, and vertex. -/
theorem fwGrowthJointPairIndex_injective {n P : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hgr : gr.length = P * 3) :
    Function.Injective (fun x : (Fin P × Fin 3) × Fin n =>
      (fwGrowthJointLayerIndex br sr wr gr hgr x.1.1 x.1.2, x.2)) := by
  rintro ⟨⟨j,k⟩, e⟩ ⟨⟨j',k'⟩, e'⟩ heq
  have hi := congrArg (fun x => x.1.val) heq
  have he := congrArg Prod.snd heq
  have hjk : finProdFinEquiv (j,k) = finProdFinEquiv (j',k') := by
    apply Fin.ext
    simp only [fwGrowthJointLayerIndex] at hi
    omega
  have hpair := finProdFinEquiv.injective hjk
  cases hpair
  cases he
  rfl

/-- The actual row growth endpoint agrees with the joint-layer pair slot. -/
theorem fw_growth_joint_row_cell {n L P : ℕ}
    (offset : ℕ) (hoff : offset + P * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (br sr wr gr gc : List (LayerPacking.Layer n))
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (j : Fin P) (k : Fin 3) (e : Fin n) (side : Bool) :
    layerPairSlot (((br ++ sr) ++ wr) ++ gr) (fwGrowthJointLayerIndex br sr wr gr hgr j k, e) side =
      fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc (k,e) false j side := by
  simp only [layerPairSlot, LayerPacking.sequenceCell, fwGrowthEdgeCells, Bool.false_eq_true,
    ↓reduceIte, btGrowingOffsetCells, fwGrowthJointLayerIndex_get, bridgeStageLayerIndex]

/-- The actual column growth endpoint is the transposed joint-layer slot. -/
theorem fw_growth_joint_column_cell {n L P : ℕ}
    (offset : ℕ) (hoff : offset + P * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (gr bc sc wc gc : List (LayerPacking.Layer n))
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (j : Fin P) (k : Fin 3) (e : Fin n) (side : Bool) :
    (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (fwGrowthJointLayerIndex bc sc wc gc hgc j k, e) side).swap =
      fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc (k,e) true j side := by
  simp only [layerPairSlot, LayerPacking.sequenceCell, fwGrowthEdgeCells, ↓reduceIte,
    btGrowingOffsetCells, fwGrowthJointLayerIndex_get, bridgeStageLayerIndex]

/-- The growth label in an existing per-edge grid is the actual combined
row-layer difference, independently of the seed-label assignment. -/
theorem fw_growth_joint_row_grid_gap {n L P : ℕ} (a : Cell n ≃ Fin (n*n))
    (offset : ℕ) (hoff : offset + P * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (br sr wr gr gc : List (LayerPacking.Layer n))
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (seedCells : Fin 16 → Bool → Cell n) (j : Fin P) (k : Fin 3) (e : Fin n) :
    fwPhysicalRowLayerGap a (((br ++ sr) ++ wr) ++ gr) (fwGrowthJointLayerIndex br sr wr gr hgr j k) e =
      fwPhysicalEdgeTraceGap a seedCells
        (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc (k,e) false) (Sum.inr j) := by
  unfold fwPhysicalRowLayerGap fwPhysicalEdgeTraceGap
  simp only [fwGrowthJointLayerIndex_get, bridgeStageLayerIndex, fwGrowthEdgeCells,
    Bool.false_eq_true, ↓reduceIte, btGrowingOffsetCells, LayerPacking.sequenceCell, LayerPacking.layerCell]

/-- The corresponding per-edge growth label equals the combined-column
physical difference in the original square. -/
theorem fw_growth_joint_column_grid_gap {n L P : ℕ} (a : Cell n ≃ Fin (n*n))
    (offset : ℕ) (hoff : offset + P * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (gr bc sc wc gc : List (LayerPacking.Layer n))
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (seedCells : Fin 16 → Bool → Cell n) (j : Fin P) (k : Fin 3) (e : Fin n) :
    fwPhysicalColumnLayerGap a (((bc ++ sc) ++ wc) ++ gc) (fwGrowthJointLayerIndex bc sc wc gc hgc j k) e =
      fwPhysicalEdgeTraceGap a seedCells
        (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc (k,e) true) (Sum.inr j) := by
  unfold fwPhysicalColumnLayerGap fwPhysicalEdgeTraceGap
  simp only [fwGrowthJointLayerIndex_get, bridgeStageLayerIndex, fwGrowthEdgeCells,
    Bool.false_eq_true, ↓reduceIte, btGrowingOffsetCells, LayerPacking.sequenceCell, LayerPacking.layerCell,
    Prod.swap_prod_mk]

/-- The combined row and column physical gaps are the actual gap recorded
by the same installed trace stage. -/
theorem fw_growth_joint_trace_gap {n L : ℕ} {stages : List BTSelectedStage}
    (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (grown : Cell n ≃ Fin (n*n))
    (hrow : ∀ (i : Fin (stages.length * 3)) (e : Fin n),
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, true))))) =
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, false))))) +
        variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e)
    (hcol : ∀ (i : Fin (stages.length * 3)) (e : Fin n),
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, true))))) =
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, false))))) +
        variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e)
    (j : Fin stages.length) (k : Fin 3) (e : Fin n) :
    fwPhysicalRowLayerGap grown (((br ++ sr) ++ wr) ++ gr) (fwGrowthJointLayerIndex br sr wr gr hgr j k) e =
        (BTStageTrace.stageAt stages rfl j).gap ∧
    fwPhysicalColumnLayerGap grown (((bc ++ sc) ++ wc) ++ gc) (fwGrowthJointLayerIndex bc sc wc gc hgc j k) e =
        (BTStageTrace.stageAt stages rfl j).gap := by
  have hr := fw_growth_edge_gap_of_installation offset hoff hs choice gr gc hgr hgc grown hrow hcol (k,e) false j
  have hc := fw_growth_edge_gap_of_installation offset hoff hs choice gr gc hgr hgc grown hrow hcol (k,e) true j
  simp only [fwGrowthEdgeCells, Bool.false_eq_true, ↓reduceIte, btGrowingOffsetCells] at hr hc
  change entry grown ((gr.get (bridgeStageLayerIndex hgr j k)).1 e, (gr.get (bridgeStageLayerIndex hgr j k)).2 e) =
    entry grown (e, (gr.get (bridgeStageLayerIndex hgr j k)).2 e) + _ at hr
  change entry grown ((gc.get (bridgeStageLayerIndex hgc j k)).2 e, (gc.get (bridgeStageLayerIndex hgc j k)).1 e) =
    entry grown ((gc.get (bridgeStageLayerIndex hgc j k)).2 e, e) + _ at hc
  constructor
  · unfold fwPhysicalRowLayerGap
    rw [fwGrowthJointLayerIndex_get]
    omega
  · unfold fwPhysicalColumnLayerGap
    rw [fwGrowthJointLayerIndex_get]
    omega

end
end Sude
