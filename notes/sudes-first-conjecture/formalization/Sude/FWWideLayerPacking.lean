import Sude.FWSeedLayerPacking

/-! Physical layer geometry for the `3*floor(n/450)` FW wide stages.
This module neither selects nor installs wide values. -/
namespace Sude
noncomputable section

/-- Adding transposed layers costs at most two cells per line per layer. -/
theorem fw_transposed_layer_union_load {n B : ℕ} {base : Finset (Cell n)}
    {layers : List (LayerPacking.Layer n)}
    (hpacked : LayerPacking.PackedLayers (LayerPacking.transposeCells base) layers)
    (hrow : ∀ i, (LayerPacking.rowUsed base i).card ≤ B)
    (hcol : ∀ i, (LayerPacking.colUsed base i).card ≤ B) :
    (∀ i, (LayerPacking.rowUsed (base ∪ LayerPacking.transposeCells
      (LayerPacking.layersSupport layers)) i).card ≤ B + 2 * layers.length) ∧
    (∀ i, (LayerPacking.colUsed (base ∪ LayerPacking.transposeCells
      (LayerPacking.layersSupport layers)) i).card ≤ B + 2 * layers.length) := by
  constructor
  · intro i
    rw [LayerPacking.rowUsed_union]
    have hu := Finset.card_union_le (LayerPacking.rowUsed base i)
      (LayerPacking.rowUsed (LayerPacking.transposeCells (LayerPacking.layersSupport layers)) i)
    have hc : (LayerPacking.rowUsed (LayerPacking.transposeCells (LayerPacking.layersSupport layers)) i).card =
        2 * layers.length := by
      rw [LayerPacking.rowUsed_card_eq, LayerPacking.transposeCells_row_card]
      exact hpacked.column_balance i
    have hb := hrow i
    omega
  · intro i
    rw [LayerPacking.colUsed_union]
    have hu := Finset.card_union_le (LayerPacking.colUsed base i)
      (LayerPacking.colUsed (LayerPacking.transposeCells (LayerPacking.layersSupport layers)) i)
    have hc : (LayerPacking.colUsed (LayerPacking.transposeCells (LayerPacking.layersSupport layers)) i).card =
        2 * layers.length := by
      rw [LayerPacking.colUsed_card_eq, LayerPacking.transposeCells_column_card]
      exact hpacked.row_balance i
    have hb := hcol i
    omega

/-- The source wide Hall guard follows from the FW lower order and the
actual integer floor `K = n / 450`. -/
theorem fw_wide_layer_hall_bound {n : ℕ} (hn : 19485 ≤ n) :
    4 * (254 + 36 * (n / 450)) + 8 < n := by
  have hdiv := Nat.div_mul_le_self n 450
  omega

/-- Given the same supplied derangement triple and already packed bridge and
seed networks, construct all `9K` row and `9K` column wide layers. Both
avoid the full RP1 support, every earlier layer, each other, and both labelled
diagonals. The exact shared stage/edge endpoints are retained. -/
theorem fw_pack_wide_layers_after_bridge_seed {n L : ℕ}
    (hn : 19485 ≤ n) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (p : Fin 3 → Equiv.Perm (Fin n)) (hder : ∀ k e, p k e ≠ e)
    (br bc sr sc : List (LayerPacking.Layer n))
    (hbrlen : br.length = 5 * 3) (hbclen : bc.length = 5 * 3)
    (hsrlen : sr.length = 16 * 3) (hsclen : sc.length = 16 * 3)
    (hbr : LayerPacking.PackedLayers (packedRectangleSupport hs choice) br)
    (hbc : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport br)) bc)
    (hsr : LayerPacking.PackedLayers
      ((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport br) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport bc)) sr)
    (hsc : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport br) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport bc)) ∪
          LayerPacking.layersSupport sr)) sc) :
    let base := (((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport br) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport bc)) ∪ LayerPacking.layersSupport sr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport sc)
    (∀ i, (LayerPacking.rowUsed base i).card ≤ 254) ∧
    (∀ i, (LayerPacking.colUsed base i).card ≤ 254) ∧
    ∃ (rows cols : List (LayerPacking.Layer n))
      (hr : rows.length = (3 * (n / 450)) * 3)
      (hc : cols.length = (3 * (n / 450)) * 3),
      rows.map Prod.fst = bridgeRepeatedPermutations (3 * (n / 450)) p ∧
      cols.map Prod.fst = bridgeRepeatedPermutations (3 * (n / 450)) p ∧
      LayerPacking.PackedLayers base rows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        (base ∪ LayerPacking.layersSupport rows)) cols ∧
      Disjoint (LayerPacking.layersSupport rows)
        (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
      (∀ z ∈ LayerPacking.layersSupport rows,
        z ∉ base ∧ z ∉ mainCells n ∧ z ∉ antiCells n) ∧
      (∀ z ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols),
        z ∉ base ∧ z ∉ mainCells n ∧ z ∉ antiCells n) ∧
      (∀ (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n),
        (rows.get (bridgeStageLayerIndex hr j k)).1 e = p k e ∧
        (cols.get (bridgeStageLayerIndex hc j k)).1 e = p k e) := by
  dsimp only
  let rect := packedRectangleSupport hs choice
  let B1 := rect ∪ LayerPacking.layersSupport br
  let B2 := B1 ∪ LayerPacking.transposeCells (LayerPacking.layersSupport bc)
  let B3 := B2 ∪ LayerPacking.layersSupport sr
  let base := B3 ∪ LayerPacking.transposeCells (LayerPacking.layersSupport sc)
  have hrow0 : ∀ i, (LayerPacking.rowUsed rect i).card ≤ 2 := packedRectangleSupport_row_load hs choice
  have hcol0 : ∀ i, (LayerPacking.colUsed rect i).card ≤ 2 := packedRectangleSupport_column_load hs choice
  obtain ⟨hr1, hc1⟩ := hbr.union_load hrow0 hcol0
  have hrow1 : ∀ i, (LayerPacking.rowUsed B1 i).card ≤ 32 := by
    intro i
    simpa [B1, rect, hbrlen] using hr1 i
  have hcol1 : ∀ i, (LayerPacking.colUsed B1 i).card ≤ 32 := by
    intro i
    simpa [B1, rect, hbrlen] using hc1 i
  obtain ⟨hr2, hc2⟩ := fw_transposed_layer_union_load hbc hrow1 hcol1
  have hrow2 : ∀ i, (LayerPacking.rowUsed B2 i).card ≤ 62 := by
    intro i
    simpa [B2, B1, rect, hbclen] using hr2 i
  have hcol2 : ∀ i, (LayerPacking.colUsed B2 i).card ≤ 62 := by
    intro i
    simpa [B2, B1, rect, hbclen] using hc2 i
  obtain ⟨hr3, hc3⟩ := hsr.union_load hrow2 hcol2
  have hrow3 : ∀ i, (LayerPacking.rowUsed B3 i).card ≤ 158 := by
    intro i
    simpa [B3, B2, B1, rect, hsrlen] using hr3 i
  have hcol3 : ∀ i, (LayerPacking.colUsed B3 i).card ≤ 158 := by
    intro i
    simpa [B3, B2, B1, rect, hsrlen] using hc3 i
  obtain ⟨hr4, hc4⟩ := fw_transposed_layer_union_load hsc hrow3 hcol3
  have hrowBase : ∀ i, (LayerPacking.rowUsed base i).card ≤ 254 := by
    intro i
    simpa [base, B3, B2, B1, rect, hsclen] using hr4 i
  have hcolBase : ∀ i, (LayerPacking.colUsed base i).card ≤ 254 := by
    intro i
    simpa [base, B3, B2, B1, rect, hsclen] using hc4 i
  let J := 3 * (n / 450)
  let perms := bridgeRepeatedPermutations J p
  have hperms : perms.length = J * 3 := bridgeRepeatedPermutations_length p
  have hder' : ∀ π ∈ perms, ∀ i, π i ≠ i := bridgeRepeatedPermutations_derange p hder
  have hguard := fw_wide_layer_hall_bound hn
  have hnrow : 4 * (254 + 2 * perms.length) + 8 < n := by
    rw [hperms]
    dsimp [J]
    omega
  obtain ⟨rows, hrmap, hrpacked⟩ := LayerPacking.pack_finite_layers perms base hder' hrowBase hcolBase hnrow
  have hr : rows.length = J * 3 := by
    have h := congrArg List.length hrmap
    simpa [hperms] using h
  obtain ⟨hrload, hcload⟩ := hrpacked.union_load hrowBase hcolBase
  have hrowT : ∀ i, (LayerPacking.rowUsed
      (LayerPacking.transposeCells (base ∪ LayerPacking.layersSupport rows)) i).card ≤ 254 + 2 * (J * 3) := by
    intro i
    simpa [hr] using hcload i
  have hcolT : ∀ i, (LayerPacking.colUsed
      (LayerPacking.transposeCells (base ∪ LayerPacking.layersSupport rows)) i).card ≤ 254 + 2 * (J * 3) := by
    intro i
    simpa [hr] using hrload i
  have hncol : 4 * ((254 + 2 * (J * 3)) + 2 * perms.length) + 8 < n := by
    rw [hperms]
    dsimp [J]
    omega
  obtain ⟨cols, hcmap, hcpacked⟩ := LayerPacking.pack_finite_layers perms
    (LayerPacking.transposeCells (base ∪ LayerPacking.layersSupport rows)) hder' hrowT hcolT hncol
  have hc : cols.length = J * 3 := by
    have h := congrArg List.length hcmap
    simpa [hperms] using h
  have hcsafe := hcpacked.transposed_support_safe
  have hdisjoint : Disjoint (LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
    apply Finset.disjoint_left.mpr
    intro z hzrow hzcol
    exact (hcsafe z hzcol).1 (Finset.mem_union_right base hzrow)
  refine ⟨hrowBase, hcolBase, rows, cols, hr, hc, hrmap, hcmap, hrpacked, hcpacked, hdisjoint, ?_, ?_, ?_⟩
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
