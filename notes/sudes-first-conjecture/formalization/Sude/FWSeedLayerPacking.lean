import Sude.FWBridgeSeedDiagonalComposition
import Sude.BridgePhysicalGrid

/-! Pack the ordinary retained-seed layer geometry after the bridge layers
in the same RP1 packing. This does not install seed values. -/
namespace Sude
noncomputable section

/-- Given the previously packed five-stage bridge layers, pack sixteen
stages of three row layers and three column layers using the same supplied
derangement triple. Every new cell avoids the full joint RP1 support and
both prior bridge networks; row and column seed networks are disjoint.
No value installation or expansion property is asserted. -/
theorem fw_pack_seed_layers_after_bridge {n L : ℕ}
    (hn : 19485 ≤ n) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (p : Fin 3 → Equiv.Perm (Fin n)) (hder : ∀ k e, p k e ≠ e)
    (br bc : List (LayerPacking.Layer n))
    (hbrlen : br.length = 5 * 3) (hbclen : bc.length = 5 * 3)
    (hbr : LayerPacking.PackedLayers (packedRectangleSupport hs choice) br)
    (hbc : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport br)) bc) :
    let base := (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport br) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport bc)
    ∃ (rows cols : List (LayerPacking.Layer n))
      (hr : rows.length = 16 * 3) (hc : cols.length = 16 * 3),
      rows.map Prod.fst = bridgeRepeatedPermutations 16 p ∧
      cols.map Prod.fst = bridgeRepeatedPermutations 16 p ∧
      LayerPacking.PackedLayers base rows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        (base ∪ LayerPacking.layersSupport rows)) cols ∧
      Disjoint (LayerPacking.layersSupport rows)
        (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
      (∀ z ∈ LayerPacking.layersSupport rows,
        z ∉ base ∧ z ∉ mainCells n ∧ z ∉ antiCells n) ∧
      (∀ z ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols),
        z ∉ base ∧ z ∉ mainCells n ∧ z ∉ antiCells n) ∧
      (∀ (j : Fin 16) (k : Fin 3) (e : Fin n),
        (rows.get (bridgeStageLayerIndex hr j k)).1 e = p k e ∧
        (cols.get (bridgeStageLayerIndex hc j k)).1 e = p k e) := by
  dsimp only
  let rect := packedRectangleSupport hs choice
  let first := rect ∪ LayerPacking.layersSupport br
  let base := first ∪ LayerPacking.transposeCells (LayerPacking.layersSupport bc)
  have hrow : ∀ i, (LayerPacking.rowUsed rect i).card ≤ 2 := packedRectangleSupport_row_load hs choice
  have hcol : ∀ i, (LayerPacking.colUsed rect i).card ≤ 2 := packedRectangleSupport_column_load hs choice
  obtain ⟨hrfirst, hcfirst⟩ := hbr.union_load hrow hcol
  have hrowBase : ∀ i, (LayerPacking.rowUsed base i).card ≤ 62 := by
    intro i
    have hcard := Finset.card_union_le (LayerPacking.rowUsed first i)
      (LayerPacking.rowUsed (LayerPacking.transposeCells (LayerPacking.layersSupport bc)) i)
    have hsecond : (LayerPacking.rowUsed (LayerPacking.transposeCells (LayerPacking.layersSupport bc)) i).card = 30 := by
      rw [LayerPacking.rowUsed_card_eq, LayerPacking.transposeCells_row_card]
      simpa [hbclen] using hbc.column_balance i
    rw [LayerPacking.rowUsed_union]
    have hf := hrfirst i
    change (LayerPacking.rowUsed first i).card ≤ 2 + 2 * br.length at hf
    rw [hbrlen] at hf
    omega
  have hcolBase : ∀ i, (LayerPacking.colUsed base i).card ≤ 62 := by
    intro i
    have hcard := Finset.card_union_le (LayerPacking.colUsed first i)
      (LayerPacking.colUsed (LayerPacking.transposeCells (LayerPacking.layersSupport bc)) i)
    have hsecond : (LayerPacking.colUsed (LayerPacking.transposeCells (LayerPacking.layersSupport bc)) i).card = 30 := by
      rw [LayerPacking.colUsed_card_eq, LayerPacking.transposeCells_column_card]
      simpa [hbclen] using hbc.row_balance i
    rw [LayerPacking.colUsed_union]
    have hf := hcfirst i
    change (LayerPacking.colUsed first i).card ≤ 2 + 2 * br.length at hf
    rw [hbrlen] at hf
    omega
  let perms := bridgeRepeatedPermutations 16 p
  have hperms : perms.length = 48 := by
    simpa [perms] using (bridgeRepeatedPermutations_length (J := 16) p)
  have hder' : ∀ π ∈ perms, ∀ i, π i ≠ i := bridgeRepeatedPermutations_derange p hder
  have hnrow : 4 * (62 + 2 * perms.length) + 8 < n := by rw [hperms]; omega
  obtain ⟨rows, hrmap, hrpacked⟩ :=
    LayerPacking.pack_finite_layers perms base hder' hrowBase hcolBase hnrow
  have hr : rows.length = 16 * 3 := by
    have h := congrArg List.length hrmap
    simpa [perms, bridgeRepeatedPermutations_length] using h
  obtain ⟨hrload, hcload⟩ := hrpacked.union_load hrowBase hcolBase
  have hrowT : ∀ i, (LayerPacking.rowUsed
      (LayerPacking.transposeCells (base ∪ LayerPacking.layersSupport rows)) i).card ≤ 158 := by
    intro i
    simpa [hr] using hcload i
  have hcolT : ∀ i, (LayerPacking.colUsed
      (LayerPacking.transposeCells (base ∪ LayerPacking.layersSupport rows)) i).card ≤ 158 := by
    intro i
    simpa [hr] using hrload i
  have hncol : 4 * (158 + 2 * perms.length) + 8 < n := by rw [hperms]; omega
  obtain ⟨cols, hcmap, hcpacked⟩ := LayerPacking.pack_finite_layers perms
    (LayerPacking.transposeCells (base ∪ LayerPacking.layersSupport rows))
    hder' hrowT hcolT hncol
  have hc : cols.length = 16 * 3 := by
    have h := congrArg List.length hcmap
    simpa [perms, bridgeRepeatedPermutations_length] using h
  have hcsafe := hcpacked.transposed_support_safe
  have hdisjoint : Disjoint (LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
    apply Finset.disjoint_left.mpr
    intro z hzrow hzcol
    exact (hcsafe z hzcol).1 (Finset.mem_union_right base hzrow)
  refine ⟨rows, cols, hr, hc, hrmap, hcmap, hrpacked, hcpacked, hdisjoint, ?_, ?_, ?_⟩
  · intro z hz
    have hoff := hrpacked.support_off_diagonals z hz
    exact ⟨fun hz' => Finset.disjoint_left.mp hrpacked.reserved_disjoint hz' hz, hoff.1, hoff.2⟩
  · intro z hz
    obtain ⟨hnot, hm, ha⟩ := hcsafe z hz
    exact ⟨fun hz' => hnot (Finset.mem_union_left _ hz'), hm, ha⟩
  · intro j k e
    exact ⟨bridgeStageLayer_endpoints rows hr p hrmap j k e,
      bridgeStageLayer_endpoints cols hc p hcmap j k e⟩

end
end Sude
