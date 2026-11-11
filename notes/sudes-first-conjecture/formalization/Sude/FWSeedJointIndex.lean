import Sude.FWJointPhysicalGaps
import Sude.FWPhysicalEdgeWitnessGrid

/-! Map actual seed stage/edge labels to the seed segment of the combined
physical network layer list. No grid, switching, or flow is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 8192

/-- The seed stage/layer index in the combined bridge/seed/wide/growth list. -/
def fwSeedJointLayerIndex {n : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (j : Fin 16) (k : Fin 3) :
    Fin (((br ++ sr) ++ wr) ++ gr).length :=
  ⟨br.length + (finProdFinEquiv (j, k)).val, by
    simp only [List.length_append]
    have hi := (finProdFinEquiv (j, k)).isLt
    omega⟩

/-- The combined-list seed index retrieves the original packed seed layer. -/
theorem fwSeedJointLayerIndex_get {n : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (j : Fin 16) (k : Fin 3) :
    (((br ++ sr) ++ wr) ++ gr).get (fwSeedJointLayerIndex br sr wr gr hsr j k) =
      sr.get (bridgeStageLayerIndex hsr j k) := by
  simp only [List.get_eq_getElem]
  unfold fwSeedJointLayerIndex bridgeStageLayerIndex
  simp only [Fin.val_cast]
  rw [List.getElem_append_left (by simp only [List.length_append]; have h := (finProdFinEquiv (j,k)).isLt; omega)]
  rw [List.getElem_append_left (by simp only [List.length_append]; have h := (finProdFinEquiv (j,k)).isLt; omega)]
  rw [List.getElem_append_right (by omega)]
  congr 1
  omega

/-- Both stage and graph-layer labels are recovered from the seed index;
the edge vertex remains the second coordinate. -/
theorem fwSeedJointPairIndex_injective {n : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) :
    Function.Injective (fun x : (Fin 16 × Fin 3) × Fin n =>
      (fwSeedJointLayerIndex br sr wr gr hsr x.1.1 x.1.2, x.2)) := by
  rintro ⟨⟨j,k⟩, e⟩ ⟨⟨j',k'⟩, e'⟩ heq
  have hi := congrArg (fun x => x.1.val) heq
  have he := congrArg Prod.snd heq
  have hjk : finProdFinEquiv (j,k) = finProdFinEquiv (j',k') := by
    apply Fin.ext
    simp only [fwSeedJointLayerIndex] at hi
    omega
  have hpair := finProdFinEquiv.injective hjk
  cases hpair
  cases he
  rfl

/-- The row-side seed endpoint is exactly the corresponding combined-layer
pair endpoint, for either side of the same physical pair. -/
theorem fw_seed_joint_row_cell {n : ℕ}
    (br sr wr gr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (j : Fin 16) (k : Fin 3) (e : Fin n) (side : Bool) :
    layerPairSlot (((br ++ sr) ++ wr) ++ gr) (fwSeedJointLayerIndex br sr wr gr hsr j k, e) side =
      fwSeedEdgeCells sr sc hsr hsc (k,e) false j side := by
  simp only [layerPairSlot, LayerPacking.sequenceCell, fwSeedEdgeCells, Bool.false_eq_true,
    ↓reduceIte, fwSeedOrdinaryCells, fwSeedJointLayerIndex_get, bridgeStageLayerIndex]

/-- Column-side seed endpoints use the transposed combined-layer slot. -/
theorem fw_seed_joint_column_cell {n : ℕ}
    (sr bc sc wc gc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (j : Fin 16) (k : Fin 3) (e : Fin n) (side : Bool) :
    (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (fwSeedJointLayerIndex bc sc wc gc hsc j k, e) side).swap =
      fwSeedEdgeCells sr sc hsr hsc (k,e) true j side := by
  simp only [layerPairSlot, LayerPacking.sequenceCell, fwSeedEdgeCells, ↓reduceIte,
    fwSeedOrdinaryCells, fwSeedJointLayerIndex_get, bridgeStageLayerIndex]

/-- The seed label gap equals the actual combined-row physical difference. -/
theorem fw_seed_joint_row_gap {n P : ℕ} (a : Cell n ≃ Fin (n*n))
    (br sr wr gr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (growthCells : Fin P → Bool → Cell n) (j : Fin 16) (k : Fin 3) (e : Fin n) :
    fwPhysicalRowLayerGap a (((br ++ sr) ++ wr) ++ gr) (fwSeedJointLayerIndex br sr wr gr hsr j k) e =
      fwPhysicalEdgeTraceGap a (fwSeedEdgeCells sr sc hsr hsc (k,e) false) growthCells (Sum.inl j) := by
  unfold fwPhysicalRowLayerGap fwPhysicalEdgeTraceGap
  simp only [fwSeedJointLayerIndex_get, bridgeStageLayerIndex, fwSeedEdgeCells,
    Bool.false_eq_true, ↓reduceIte, fwSeedOrdinaryCells, LayerPacking.sequenceCell, LayerPacking.layerCell]

/-- The seed label gap equals the actual combined-column physical difference. -/
theorem fw_seed_joint_column_gap {n P : ℕ} (a : Cell n ≃ Fin (n*n))
    (sr bc sc wc gc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (growthCells : Fin P → Bool → Cell n) (j : Fin 16) (k : Fin 3) (e : Fin n) :
    fwPhysicalColumnLayerGap a (((bc ++ sc) ++ wc) ++ gc) (fwSeedJointLayerIndex bc sc wc gc hsc j k) e =
      fwPhysicalEdgeTraceGap a (fwSeedEdgeCells sr sc hsr hsc (k,e) true) growthCells (Sum.inl j) := by
  unfold fwPhysicalColumnLayerGap fwPhysicalEdgeTraceGap
  simp only [fwSeedJointLayerIndex_get, bridgeStageLayerIndex, fwSeedEdgeCells,
    Bool.false_eq_true, ↓reduceIte, fwSeedOrdinaryCells, LayerPacking.sequenceCell, LayerPacking.layerCell,
    Prod.swap_prod_mk]

end
end Sude
