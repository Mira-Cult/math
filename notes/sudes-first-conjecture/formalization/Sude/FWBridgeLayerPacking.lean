import Sude.BridgeNetworkAfterRectangles
import Sude.LayerTranspose

/-! Conditional FW bridge network geometry. The supplied permutation lists
must already be derangements; no expansion or other controller property is
asserted. All joint RP1 rectangle cells are excluded from both networks. -/
namespace Sude
noncomputable section

/-- Pack five stages of three row and three column layers around the complete
joint rectangle support. Both networks are physically disjoint, avoid both
labelled diagonals, and keep the supplied permutation lists. This is a
geometric existence statement; it neither installs values nor constructs the
supplied permutations or any future layout. -/
theorem fw_pack_bridge_layers_around_rectangles {n L : ℕ}
    (hn : 19485 ≤ n) (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (otherChoice : Fin L → Bool)
    (rowPerms colPerms : List (Equiv.Perm (Fin n)))
    (hrlen : rowPerms.length = 15) (hclen : colPerms.length = 15)
    (hrderange : ∀ π ∈ rowPerms, ∀ i, π i ≠ i)
    (hcderange : ∀ π ∈ colPerms, ∀ i, π i ≠ i) :
    ∃ rows cols : List (LayerPacking.Layer n),
      rows.map Prod.fst = rowPerms ∧ cols.map Prod.fst = colPerms ∧
      LayerPacking.PackedLayers
        (packedRectangleSupport hs (bridgeDiagonalChoice hrect otherChoice)) rows ∧
      LayerPacking.PackedLayers
        (LayerPacking.transposeCells
          (packedRectangleSupport hs (bridgeDiagonalChoice hrect otherChoice) ∪
            LayerPacking.layersSupport rows)) cols ∧
      Disjoint (LayerPacking.layersSupport rows)
        (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
      (∀ z ∈ LayerPacking.layersSupport rows,
        z ∉ packedRectangleSupport hs (bridgeDiagonalChoice hrect otherChoice) ∧
        z ∉ mainCells n ∧ z ∉ antiCells n) ∧
      (∀ z ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols),
        z ∉ packedRectangleSupport hs (bridgeDiagonalChoice hrect otherChoice) ∧
        z ∉ mainCells n ∧ z ∉ antiCells n) := by
  let reserved := packedRectangleSupport hs (bridgeDiagonalChoice hrect otherChoice)
  have hrow : ∀ i, (LayerPacking.rowUsed reserved i).card ≤ 2 :=
    packedRectangleSupport_row_load hs _
  have hcol : ∀ i, (LayerPacking.colUsed reserved i).card ≤ 2 :=
    packedRectangleSupport_column_load hs _
  have hnrow : 4 * (2 + 2 * rowPerms.length) + 8 < n := by rw [hrlen]; omega
  obtain ⟨rows, hrmap, hrpacked⟩ :=
    LayerPacking.pack_finite_layers rowPerms reserved hrderange hrow hcol hnrow
  have hrowslen : rows.length = rowPerms.length := by
    have h := congrArg List.length hrmap
    simpa using h
  obtain ⟨hrow', hcol'⟩ := hrpacked.union_load hrow hcol
  have hrowT : ∀ i, (LayerPacking.rowUsed
      (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows)) i).card ≤ 32 := by
    intro i
    simpa [hrowslen, hrlen] using hcol' i
  have hcolT : ∀ i, (LayerPacking.colUsed
      (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows)) i).card ≤ 32 := by
    intro i
    simpa [hrowslen, hrlen] using hrow' i
  have hncol : 4 * (32 + 2 * colPerms.length) + 8 < n := by rw [hclen]; omega
  obtain ⟨cols, hcmap, hcpacked⟩ := LayerPacking.pack_finite_layers colPerms
    (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows))
    hcderange hrowT hcolT hncol
  have hcsafe := hcpacked.transposed_support_safe
  have hdisjoint : Disjoint (LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
    apply Finset.disjoint_left.mpr
    intro z hzr hzc
    exact (hcsafe z hzc).1 (Finset.mem_union_right reserved hzr)
  refine ⟨rows, cols, hrmap, hcmap, hrpacked, hcpacked, hdisjoint, ?_, ?_⟩
  · intro z hz
    have hoff := hrpacked.support_off_diagonals z hz
    exact ⟨fun hz' => Finset.disjoint_left.mp hrpacked.reserved_disjoint hz' hz,
      hoff.1, hoff.2⟩
  · intro z hz
    obtain ⟨hnot, hm, ha⟩ := hcsafe z hz
    exact ⟨fun hz' => hnot (Finset.mem_union_left _ hz'), hm, ha⟩

end
end Sude
