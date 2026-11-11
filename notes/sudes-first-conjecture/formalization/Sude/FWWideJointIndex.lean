import Sude.FWJointPhysicalGaps
import Sude.FWWideEdgeRoles

/-! Map selected wide-stage labels to the combined physical network layers.
This does not transport grids, choose switches, or construct flow. -/
namespace Sude
noncomputable section
set_option maxRecDepth 8192

/-- Wide stage/layer index in the combined bridge/seed/wide/growth list. -/
def fwWideJointLayerIndex {n : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (k : Fin 3) :
    Fin (((br ++ sr) ++ wr) ++ gr).length :=
  ⟨br.length + sr.length + (finProdFinEquiv (j,k)).val, by
    simp only [List.length_append]
    have hi := (finProdFinEquiv (j,k)).isLt
    omega⟩

/-- The joint index retrieves the original physical wide layer. -/
theorem fwWideJointLayerIndex_get {n : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (k : Fin 3) :
    (((br ++ sr) ++ wr) ++ gr).get (fwWideJointLayerIndex br sr wr gr hwr j k) =
      wr.get (bridgeStageLayerIndex hwr j k) := by
  simp only [List.get_eq_getElem]
  unfold fwWideJointLayerIndex bridgeStageLayerIndex
  simp only [Fin.val_cast]
  rw [List.getElem_append_left (by simp only [List.length_append]; have h := (finProdFinEquiv (j,k)).isLt; omega)]
  rw [List.getElem_append_right (by simp only [List.length_append]; omega)]
  congr 1
  simp only [List.length_append]
  omega

/-- The joint pair labels recover the wide stage, graph layer, and vertex. -/
theorem fwWideJointPairIndex_injective {n : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3) :
    Function.Injective (fun x : (Fin (3 * (n / 450)) × Fin 3) × Fin n =>
      (fwWideJointLayerIndex br sr wr gr hwr x.1.1 x.1.2, x.2)) := by
  rintro ⟨⟨j,k⟩, e⟩ ⟨⟨j',k'⟩, e'⟩ heq
  have hi := congrArg (fun x => x.1.val) heq
  have he := congrArg Prod.snd heq
  have hjk : finProdFinEquiv (j,k) = finProdFinEquiv (j',k') := by
    apply Fin.ext
    simp only [fwWideJointLayerIndex] at hi
    omega
  have hpair := finProdFinEquiv.injective hjk
  cases hpair
  cases he
  rfl

/-- The actual row wide endpoint is its combined-layer pair slot. -/
theorem fw_wide_joint_row_cell {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br sr wr gr wc : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n) (side : Bool) :
    layerPairSlot (((br ++ sr) ++ wr) ++ gr) (fwWideJointLayerIndex br sr wr gr hwr j k, e) side =
      fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e false side) := by
  simp only [layerPairSlot, LayerPacking.sequenceCell, fwWidePhysicalCells, fwWideEdgeRole,
    Sum.elim_inr, fwWideOrdinaryCells, Bool.false_eq_true, ↓reduceIte, fwWideLayerIndex,
    fwWideJointLayerIndex_get, bridgeStageLayerIndex]

/-- The actual column wide endpoint is the transposed combined-layer slot. -/
theorem fw_wide_joint_column_cell {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (wr bc sc wc gc : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n) (side : Bool) :
    (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (fwWideJointLayerIndex bc sc wc gc hwc j k, e) side).swap =
      fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e true side) := by
  simp only [layerPairSlot, LayerPacking.sequenceCell, fwWidePhysicalCells, fwWideEdgeRole,
    Sum.elim_inr, fwWideOrdinaryCells, ↓reduceIte, fwWideLayerIndex,
    fwWideJointLayerIndex_get, bridgeStageLayerIndex]

/-- A supplied selected wide gap is exactly the actual combined-layer gap
on both networks; the pair equations refer to the same square and roles. -/
theorem fw_wide_joint_selected_gap {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (grown : Cell n ≃ Fin (n*n))
    (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n) (gap : ℕ)
    (hpair : ∀ network : Bool,
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e network true)) =
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e network false)) + gap) :
    fwPhysicalRowLayerGap grown (((br ++ sr) ++ wr) ++ gr) (fwWideJointLayerIndex br sr wr gr hwr j k) e = gap ∧
    fwPhysicalColumnLayerGap grown (((bc ++ sc) ++ wc) ++ gc) (fwWideJointLayerIndex bc sc wc gc hwc j k) e = gap := by
  have hr := hpair false
  have hc := hpair true
  simp only [fwWidePhysicalCells, fwWideEdgeRole, Sum.elim_inr, fwWideOrdinaryCells,
    Bool.false_eq_true, ↓reduceIte, fwWideLayerIndex] at hr hc
  change entry grown ((wr.get (bridgeStageLayerIndex hwr j k)).1 e, (wr.get (bridgeStageLayerIndex hwr j k)).2 e) =
    entry grown (e, (wr.get (bridgeStageLayerIndex hwr j k)).2 e) + gap at hr
  change entry grown ((wc.get (bridgeStageLayerIndex hwc j k)).2 e, (wc.get (bridgeStageLayerIndex hwc j k)).1 e) =
    entry grown ((wc.get (bridgeStageLayerIndex hwc j k)).2 e, e) + gap at hc
  constructor
  · unfold fwPhysicalRowLayerGap
    rw [fwWideJointLayerIndex_get]
    omega
  · unfold fwPhysicalColumnLayerGap
    rw [fwWideJointLayerIndex_get]
    omega

end
end Sude
