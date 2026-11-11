import Sude.FWBridgeLayerPacking

/-! Reindex the packed FW bridge layers by their actual stage and slot labels.
This establishes physical cell geometry only. -/
namespace Sude
noncomputable section

/-- Reindex a stage, within-stage layer, edge and side into a packed list. -/
def fwBridgeLayerIndex {n m : ℕ} (hlen : m = 5 * 3)
    (x : (Fin 5 × (Fin 3 × Fin n)) × Bool) : Fin m × (Fin n × Bool) :=
  (Fin.cast hlen.symm (finProdFinEquiv (x.1.1, x.1.2.1)), (x.1.2.2, x.2))

theorem fwBridgeLayerIndex_injective {n m : ℕ} (hlen : m = 5 * 3) :
    Function.Injective (fwBridgeLayerIndex (n := n) hlen) := by
  rintro ⟨⟨j, k, e⟩, s⟩ ⟨⟨j', k', e'⟩, s'⟩ h
  have hi := congrArg Prod.fst h
  have he := congrArg (fun z : Fin m × (Fin n × Bool) => z.2.1) h
  have hs := congrArg (fun z : Fin m × (Fin n × Bool) => z.2.2) h
  have hjk : (j, k) = (j', k') := by
    apply finProdFinEquiv.injective
    exact Fin.cast_injective hlen.symm hi
  cases hjk
  cases he
  cases hs
  rfl

/-- Row slots use the row layers; column slots use the transposed layers. -/
def fwBridgeLayerCells {n : ℕ} (rows cols : List (LayerPacking.Layer n))
    (hrlen : rows.length = 5 * 3) (hclen : cols.length = 5 * 3)
    (x : (Fin 5 × (Fin 3 × Fin n)) × (Bool × Bool)) : Cell n :=
  if x.2.1 then
    (LayerPacking.sequenceCell cols (fwBridgeLayerIndex hclen (x.1, x.2.2))).swap
  else LayerPacking.sequenceCell rows (fwBridgeLayerIndex hrlen (x.1, x.2.2))

/-- A conditional packing yields the FW ordinary cell map, injective and
free of every joint RP1 rectangle corner. No expansion or placement of
values is asserted. -/
theorem fw_bridge_layer_cells_exist {n L : ℕ}
    (hn : 19485 ≤ n) (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (otherChoice : Fin L → Bool)
    (rowPerms colPerms : List (Equiv.Perm (Fin n)))
    (hrlen : rowPerms.length = 15) (hclen : colPerms.length = 15)
    (hrderange : ∀ π ∈ rowPerms, ∀ i, π i ≠ i)
    (hcderange : ∀ π ∈ colPerms, ∀ i, π i ≠ i) :
    ∃ (rows cols : List (LayerPacking.Layer n))
      (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3),
      rows.map Prod.fst = rowPerms ∧ cols.map Prod.fst = colPerms ∧
      LayerPacking.PackedLayers
        (packedRectangleSupport hs (bridgeDiagonalChoice hrect otherChoice)) rows ∧
      LayerPacking.PackedLayers
        (LayerPacking.transposeCells
          (packedRectangleSupport hs (bridgeDiagonalChoice hrect otherChoice) ∪
            LayerPacking.layersSupport rows)) cols ∧
      Function.Injective (fwBridgeLayerCells rows cols hr hc) ∧
      (∀ x, fwBridgeLayerCells rows cols hr hc x ∉
        packedRectangleSupport hs (bridgeDiagonalChoice hrect otherChoice)) ∧
      (∀ x (t : Fin L) side, fwBridgeLayerCells rows cols hr hc x ≠
        packedRectangleCorner hs (bridgeDiagonalChoice hrect otherChoice) (t, side)) := by
  obtain ⟨rows, cols, hrmap, hcmap, hrpacked, hcpacked, hdisjoint, hrsafe, hcsafe⟩ :=
    fw_pack_bridge_layers_around_rectangles hn hrect hs otherChoice rowPerms colPerms
      hrlen hclen hrderange hcderange
  have hr : rows.length = 5 * 3 := by
    have h := congrArg List.length hrmap
    simpa [hrlen] using h
  have hc : cols.length = 5 * 3 := by
    have h := congrArg List.length hcmap
    simpa [hclen] using h
  have hrmem : ∀ x, LayerPacking.sequenceCell rows x ∈ LayerPacking.layersSupport rows := by
    intro x
    exact LayerPacking.layerSupport_subset (rows.get x.1) rows (List.get_mem rows x.1)
      (LayerPacking.sequenceCell_mem rows x.1 x.2)
  have hcmem : ∀ x, (LayerPacking.sequenceCell cols x).swap ∈
      LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
    intro x
    exact Finset.mem_image.mpr ⟨_, LayerPacking.layerSupport_subset (cols.get x.1) cols
      (List.get_mem cols x.1) (LayerPacking.sequenceCell_mem cols x.1 x.2), rfl⟩
  have hinj : Function.Injective (fwBridgeLayerCells rows cols hr hc) := by
    rintro ⟨a, ⟨network, side⟩⟩ ⟨b, ⟨network', side'⟩⟩ heq
    cases network <;> cases network'
    · simp only [fwBridgeLayerCells, Bool.false_eq_true, ↓reduceIte] at heq
      have hidx := (fwBridgeLayerIndex_injective hr) (hrpacked.sequenceCell_injective heq)
      cases hidx
      rfl
    · simp only [fwBridgeLayerCells, Bool.false_eq_true, ↓reduceIte] at heq
      exact False.elim (Finset.disjoint_left.mp hdisjoint (hrmem _) (heq ▸ hcmem _))
    · simp only [fwBridgeLayerCells, Bool.false_eq_true, ↓reduceIte] at heq
      exact False.elim (Finset.disjoint_left.mp hdisjoint (heq ▸ hrmem _) (hcmem _))
    · simp only [fwBridgeLayerCells, ↓reduceIte] at heq
      have heq' := congrArg Prod.swap heq
      simp only [Prod.swap_swap] at heq'
      have hidx := (fwBridgeLayerIndex_injective hc) (hcpacked.sequenceCell_injective heq')
      cases hidx
      rfl
  have hfree : ∀ x, fwBridgeLayerCells rows cols hr hc x ∉
      packedRectangleSupport hs (bridgeDiagonalChoice hrect otherChoice) := by
    rintro ⟨a, ⟨network, side⟩⟩
    cases network
    · exact (hrsafe _ (hrmem _)).1
    · exact (hcsafe _ (hcmem _)).1
  refine ⟨rows, cols, hr, hc, hrmap, hcmap, hrpacked, hcpacked, hinj, hfree, ?_⟩
  intro x t side heq
  apply hfree x
  rw [heq]
  exact Finset.mem_image.mpr ⟨(t, side), Finset.mem_univ _, rfl⟩

end
end Sude
