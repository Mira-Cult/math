import Sude.FWJointPhysicalGaps
import Sude.FWPhysicalBridgeWideTrace

/-! Map the five actual bridge stages to their original segment in the
combined physical network lists. No grid transport or flow is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 8192

/-- Convert a bridge-grid label to a stage only after proving it lies in the
actual five-stage support. -/
def fwBridgeSupportStage (j : {j : ℕ // j ∈ Finset.range 5}) : Fin 5 :=
  ⟨j.1, Finset.mem_range.mp j.2⟩

@[simp] theorem fwBridgeSupportStage_val (j : {j : ℕ // j ∈ Finset.range 5}) :
    (fwBridgeSupportStage j).val = j.1 := rfl

/-- Restricting natural labels to the actual support loses no stage identity. -/
theorem fwBridgeSupportStage_injective : Function.Injective fwBridgeSupportStage := by
  intro x y h
  exact Subtype.ext (congrArg Fin.val h)

/-- The support conversion preserves the bridge summand's selected gap. -/
theorem fwBridgeSupportStage_joined_gap {α : Type*} (initialGap : α → ℕ)
    (batches : ℕ → List DoublePair) (index : ℕ)
    (j : {j : ℕ // j ∈ Finset.range 5}) :
    joinedBridgeGap initialGap batches index (Sum.inr j.1) =
      selectedBridgeGap batches index (fwBridgeSupportStage j).val := rfl

/-- The actual bridge stage/layer index within the combined list. -/
def fwBridgeJointLayerIndex {n : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (j : Fin 5) (k : Fin 3) :
    Fin (((br ++ sr) ++ wr) ++ gr).length :=
  ⟨(finProdFinEquiv (j, k)).val, by
    simp only [List.length_append]
    have hi := (finProdFinEquiv (j,k)).isLt
    omega⟩

/-- The joint index retrieves the same physical bridge layer. -/
theorem fwBridgeJointLayerIndex_get {n : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (j : Fin 5) (k : Fin 3) :
    (((br ++ sr) ++ wr) ++ gr).get (fwBridgeJointLayerIndex br sr wr gr hbr j k) =
      br.get (bridgeStageLayerIndex hbr j k) := by
  simp only [List.get_eq_getElem]
  unfold fwBridgeJointLayerIndex bridgeStageLayerIndex
  simp only [Fin.val_cast]
  rw [List.getElem_append_left (by simp only [List.length_append]; have h := (finProdFinEquiv (j,k)).isLt; omega)]
  rw [List.getElem_append_left (by simp only [List.length_append]; have h := (finProdFinEquiv (j,k)).isLt; omega)]
  rw [List.getElem_append_left (by have h := (finProdFinEquiv (j,k)).isLt; omega)]

/-- The joint pair labels recover bridge stage, graph layer, and vertex. -/
theorem fwBridgeJointPairIndex_injective {n : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) :
    Function.Injective (fun x : (Fin 5 × Fin 3) × Fin n =>
      (fwBridgeJointLayerIndex br sr wr gr hbr x.1.1 x.1.2, x.2)) := by
  rintro ⟨⟨j,k⟩, e⟩ ⟨⟨j',k'⟩, e'⟩ heq
  have hi := congrArg (fun x => x.1.val) heq
  have he := congrArg Prod.snd heq
  have hjk : finProdFinEquiv (j,k) = finProdFinEquiv (j',k') := by
    apply Fin.ext
    simpa only [fwBridgeJointLayerIndex] using hi
  have hpair := finProdFinEquiv.injective hjk
  cases hpair
  cases he
  rfl

/-- A bridge row endpoint is exactly its combined-row physical pair slot. -/
theorem fw_bridge_joint_row_cell {n : ℕ}
    (br sr wr gr bc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (j : Fin 5) (k : Fin 3) (e : Fin n) (side : Bool) :
    layerPairSlot (((br ++ sr) ++ wr) ++ gr) (fwBridgeJointLayerIndex br sr wr gr hbr j k, e) side =
      fwBridgeLayerCells br bc hbr hbc ((j,(k,e)),(false,side)) := by
  simp only [layerPairSlot, LayerPacking.sequenceCell, fwBridgeLayerCells, Bool.false_eq_true,
    ↓reduceIte, fwBridgeLayerIndex, fwBridgeJointLayerIndex_get, bridgeStageLayerIndex]

/-- A bridge column endpoint is its transposed combined-column physical slot. -/
theorem fw_bridge_joint_column_cell {n : ℕ}
    (br bc sc wc gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (j : Fin 5) (k : Fin 3) (e : Fin n) (side : Bool) :
    (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (fwBridgeJointLayerIndex bc sc wc gc hbc j k, e) side).swap =
      fwBridgeLayerCells br bc hbr hbc ((j,(k,e)),(true,side)) := by
  simp only [layerPairSlot, LayerPacking.sequenceCell, fwBridgeLayerCells, ↓reduceIte,
    fwBridgeLayerIndex, fwBridgeJointLayerIndex_get, bridgeStageLayerIndex]

/-- On the preserved physical square, the joint row and column gap values
are both the selected gap of this exact bridge batch and graph edge. -/
theorem fw_bridge_joint_selected_gap {n L : ℕ}
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc : List (LayerPacking.Layer n)) (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3)
    (old grown : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hr hc sr sc hsr hsc wr wc hwr hwc,
      entry grown c = entry old c)
    (hplace : ∀ x, entry old (fwBridgeLayerCells br bc hr hc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x))
    (gr gc : List (LayerPacking.Layer n)) (j : Fin 5) (k : Fin 3) (e : Fin n) :
    let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) (k,e)
    fwPhysicalRowLayerGap grown (((br ++ sr) ++ wr) ++ gr) (fwBridgeJointLayerIndex br sr wr gr hr j k) e =
        selectedBridgeGap batches index j ∧
    fwPhysicalColumnLayerGap grown (((bc ++ sc) ++ wc) ++ gc) (fwBridgeJointLayerIndex bc sc wc gc hc j k) e =
        selectedBridgeGap batches index j := by
  dsimp only
  have hrow := (fw_preserved_bridge_ordinary_gap batches hvalid hrect hseed hwide hs choice
    br bc hr hc sr sc hsr hsc wr wc hwr hwc old grown hfixed hplace j (k,e) false).2.2
  have hcol := (fw_preserved_bridge_ordinary_gap batches hvalid hrect hseed hwide hs choice
    br bc hr hc sr sc hsr hsc wr wc hwr hwc old grown hfixed hplace j (k,e) true).2.2
  simp only [fwBridgeLayerCells, Bool.false_eq_true, ↓reduceIte, fwBridgeLayerIndex] at hrow hcol
  change entry grown ((br.get (bridgeStageLayerIndex hr j k)).1 e, (br.get (bridgeStageLayerIndex hr j k)).2 e) =
    entry grown (e, (br.get (bridgeStageLayerIndex hr j k)).2 e) + _ at hrow
  change entry grown ((bc.get (bridgeStageLayerIndex hc j k)).2 e, (bc.get (bridgeStageLayerIndex hc j k)).1 e) =
    entry grown ((bc.get (bridgeStageLayerIndex hc j k)).2 e, e) + _ at hcol
  constructor
  · unfold fwPhysicalRowLayerGap
    rw [fwBridgeJointLayerIndex_get]
    omega
  · unfold fwPhysicalColumnLayerGap
    rw [fwBridgeJointLayerIndex_get]
    omega

end
end Sude
