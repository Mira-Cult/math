import Sude.NetworkSwitchPairEndpoints

/-! Pair endpoint identity-or-reversal in the SAME two-network switch outcome. -/
namespace Sude
noncomputable section

theorem toggle_two_installed_networks_preserves_pair_endpoints {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (rows cols : List (LayerPacking.Layer n))
    (hr : LayerPacking.PackedLayers reserved rows)
    (hc : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows)) cols)
    (rowGap : Fin rows.length → Fin n → ℕ)
    (colGap : Fin cols.length → Fin n → ℕ)
    (hrowGap : ∀ i e, entry a ((rows.get i).1 e, (rows.get i).2 e) =
      entry a (e, (rows.get i).2 e) + rowGap i e)
    (hcolGap : ∀ i e, entry a ((cols.get i).2 e, (cols.get i).1 e) =
      entry a ((cols.get i).2 e, e) + colGap i e)
    (Sr : Finset (Fin rows.length × Fin n))
    (Sc : Finset (Fin cols.length × Fin n)) :
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ r, (rowSum b r : ℤ) - (rowSum a r : ℤ) = ∑ k ∈ Sr, layerTransfer rows rowGap k r) ∧
      (∀ c, (columnSum b c : ℤ) - (columnSum a c : ℤ) = ∑ k ∈ Sc, layerTransfer cols colGap k c) ∧
      mainSum b = mainSum a ∧ antiSum b = antiSum a ∧
      (∀ c ∈ reserved, entry b c = entry a c) ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) ∧
      (∀ k, entry b (layerPairSlot rows k false) + entry b (layerPairSlot rows k true) =
        entry a (layerPairSlot rows k false) + entry a (layerPairSlot rows k true)) ∧
      (∀ k, entry b ((layerPairSlot cols k false).swap) + entry b ((layerPairSlot cols k true).swap) =
        entry a ((layerPairSlot cols k false).swap) + entry a ((layerPairSlot cols k true).swap)) ∧
      (∀ k, (entry b (layerPairSlot rows k false) = entry a (layerPairSlot rows k false) ∧
             entry b (layerPairSlot rows k true) = entry a (layerPairSlot rows k true)) ∨
            (entry b (layerPairSlot rows k false) = entry a (layerPairSlot rows k true) ∧
             entry b (layerPairSlot rows k true) = entry a (layerPairSlot rows k false))) ∧
      (∀ k, (entry b ((layerPairSlot cols k false).swap) = entry a ((layerPairSlot cols k false).swap) ∧
             entry b ((layerPairSlot cols k true).swap) = entry a ((layerPairSlot cols k true).swap)) ∨
            (entry b ((layerPairSlot cols k false).swap) = entry a ((layerPairSlot cols k true).swap) ∧
             entry b ((layerPairSlot cols k true).swap) = entry a ((layerPairSlot cols k false).swap))) := by
  let vr := hr.rowPairs a rowGap hrowGap
  obtain ⟨br, hR, hRpair⟩ := rowNetwork_toggle_subset_preserves_pair_endpoints a vr Sr
  have hcolumn_unchanged : ∀ z ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols),
      entry br z = entry a z := by
    intro z hz
    have hs := hc.transposed_support_safe z hz
    apply hR.outside_fixed z
    intro k hk
    constructor
    · intro heq
      have hmem := layerPairSlot_mem rows k false
      change (k.2, (rows.get k.1).2 k.2) ∈ LayerPacking.layersSupport rows at hmem
      apply hs.1
      apply Finset.mem_union_right reserved
      simpa [vr, LayerPacking.PackedLayers.rowPairs] using heq ▸ hmem
    · intro heq
      have hmem := layerPairSlot_mem rows k true
      change ((rows.get k.1).1 k.2, (rows.get k.1).2 k.2) ∈ LayerPacking.layersSupport rows at hmem
      apply hs.1
      apply Finset.mem_union_right reserved
      simpa [vr, LayerPacking.PackedLayers.rowPairs] using heq ▸ hmem
  have hcolGap' : ∀ i e, entry br ((cols.get i).2 e, (cols.get i).1 e) =
      entry br ((cols.get i).2 e, e) + colGap i e := by
    intro i e
    have hlow := hcolumn_unchanged _ (transposedLayerPairSlot_mem cols (i, e) false)
    have hhigh := hcolumn_unchanged _ (transposedLayerPairSlot_mem cols (i, e) true)
    change entry br ((cols.get i).2 e, e) = entry a ((cols.get i).2 e, e) at hlow
    change entry br ((cols.get i).2 e, (cols.get i).1 e) =
      entry a ((cols.get i).2 e, (cols.get i).1 e) at hhigh
    rw [hhigh, hlow]
    exact hcolGap i e
  let vc := hc.columnPairs br colGap hcolGap'
  obtain ⟨b, hC, hCpair⟩ := columnNetwork_toggle_subset_preserves_pair_endpoints br vc Sc
  have hrowEnds : ∀ k,
      (entry b (layerPairSlot rows k false) = entry a (layerPairSlot rows k false) ∧
       entry b (layerPairSlot rows k true) = entry a (layerPairSlot rows k true)) ∨
      (entry b (layerPairSlot rows k false) = entry a (layerPairSlot rows k true) ∧
       entry b (layerPairSlot rows k true) = entry a (layerPairSlot rows k false)) := by
    intro k
    have hunchanged : ∀ side, entry b (layerPairSlot rows k side) = entry br (layerPairSlot rows k side) := by
      intro side
      apply hC.outside_fixed
      intro l hl
      constructor
      · intro heq
        have hcol : (vc.column l, vc.low l) ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
          simpa [vc, layerPairSlot, LayerPacking.sequenceCell, LayerPacking.layerCell,
            LayerPacking.PackedLayers.columnPairs, LayerPacking.PackedLayers.rowPairs] using
              transposedLayerPairSlot_mem cols l false
        have hbad := hc.transposed_support_safe _ (heq ▸ hcol)
        exact hbad.1 (Finset.mem_union_right reserved (layerPairSlot_mem rows k side))
      · intro heq
        have hcol : (vc.column l, vc.high l) ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
          simpa [vc, layerPairSlot, LayerPacking.sequenceCell, LayerPacking.layerCell,
            LayerPacking.PackedLayers.columnPairs, LayerPacking.PackedLayers.rowPairs] using
              transposedLayerPairSlot_mem cols l true
        have hbad := hc.transposed_support_safe _ (heq ▸ hcol)
        exact hbad.1 (Finset.mem_union_right reserved (layerPairSlot_mem rows k side))
    rw [hunchanged false, hunchanged true]
    simpa [vr, layerPairSlot, LayerPacking.sequenceCell, LayerPacking.layerCell,
      LayerPacking.PackedLayers.rowPairs] using hRpair k
  have hcolEnds : ∀ k,
      (entry b ((layerPairSlot cols k false).swap) = entry a ((layerPairSlot cols k false).swap) ∧
       entry b ((layerPairSlot cols k true).swap) = entry a ((layerPairSlot cols k true).swap)) ∨
      (entry b ((layerPairSlot cols k false).swap) = entry a ((layerPairSlot cols k true).swap) ∧
       entry b ((layerPairSlot cols k true).swap) = entry a ((layerPairSlot cols k false).swap)) := by
    intro k
    have hlo := hcolumn_unchanged _ (transposedLayerPairSlot_mem cols k false)
    have hhi := hcolumn_unchanged _ (transposedLayerPairSlot_mem cols k true)
    have hp := hCpair k
    change (entry b ((layerPairSlot cols k false).swap) = entry br ((layerPairSlot cols k false).swap) ∧
            entry b ((layerPairSlot cols k true).swap) = entry br ((layerPairSlot cols k true).swap)) ∨
           (entry b ((layerPairSlot cols k false).swap) = entry br ((layerPairSlot cols k true).swap) ∧
            entry b ((layerPairSlot cols k true).swap) = entry br ((layerPairSlot cols k false).swap)) at hp
    rw [hlo, hhi] at hp
    exact hp
  refine ⟨b, ?_, ?_, hC.main.trans hR.main, hC.anti.trans hR.anti, ?_, entry_range _, entry_injective _, ?_, ?_, hrowEnds, hcolEnds⟩
  · intro r
    rw [hC.rows r]
    exact hR.rows r
  · intro c
    have hh := hC.columns c
    rw [hR.columns c] at hh
    change (columnSum b c : ℤ) - (columnSum a c : ℤ) = ∑ k ∈ Sc, layerTransfer cols colGap k c
    exact hh
  · intro z hz
    have hRfixed : entry br z = entry a z := by
      apply hR.outside_fixed z
      intro k hk
      constructor
      · intro heq
        have hmem := layerPairSlot_mem rows k false
        change (k.2, (rows.get k.1).2 k.2) ∈ LayerPacking.layersSupport rows at hmem
        have hzmem : z ∈ LayerPacking.layersSupport rows := by
          simpa [vr, LayerPacking.PackedLayers.rowPairs] using heq ▸ hmem
        exact Finset.disjoint_left.mp hr.reserved_disjoint hz hzmem
      · intro heq
        have hmem := layerPairSlot_mem rows k true
        change ((rows.get k.1).1 k.2, (rows.get k.1).2 k.2) ∈ LayerPacking.layersSupport rows at hmem
        have hzmem : z ∈ LayerPacking.layersSupport rows := by
          simpa [vr, LayerPacking.PackedLayers.rowPairs] using heq ▸ hmem
        exact Finset.disjoint_left.mp hr.reserved_disjoint hz hzmem
    have hCfixed : entry b z = entry br z := by
      apply hC.outside_fixed z
      intro k hk
      constructor
      · intro heq
        have hmem := transposedLayerPairSlot_mem cols k false
        change ((cols.get k.1).2 k.2, k.2) ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols) at hmem
        have hzmem : z ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
          simpa [vc, LayerPacking.PackedLayers.columnPairs, LayerPacking.PackedLayers.rowPairs] using heq ▸ hmem
        exact (hc.transposed_support_safe z hzmem).1 (Finset.mem_union_left _ hz)
      · intro heq
        have hmem := transposedLayerPairSlot_mem cols k true
        change ((cols.get k.1).2 k.2, (cols.get k.1).1 k.2) ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols) at hmem
        have hzmem : z ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
          simpa [vc, LayerPacking.PackedLayers.columnPairs, LayerPacking.PackedLayers.rowPairs] using heq ▸ hmem
        exact (hc.transposed_support_safe z hzmem).1 (Finset.mem_union_left _ hz)
    exact hCfixed.trans hRfixed

  · intro k
    rcases hrowEnds k with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega
  · intro k
    rcases hcolEnds k with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> omega

end
end Sude
