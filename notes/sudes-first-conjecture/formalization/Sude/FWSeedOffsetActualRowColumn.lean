import Sude.FWSeedOffsetActualDiagonal
import Sude.FWSeedOffsetRowColumnRectangle

/-! Actual offset seed pair incidence on rows and columns. -/
namespace Sude
noncomputable section

/-- Actual ordinary row slot for the offset seed allocation. -/
theorem fw_seed_existing_row_cell {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (j : Fin 16) (k : Fin 3) (edge : Fin n) (side : Bool) :
    fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      ((j, prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (0, k, edge)), side) =
    LayerPacking.layerCell (prefixStageLayer sr hsr j k).1
      (prefixStageLayer sr hsr j k).2 (edge, side) := by
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let e := Equiv.ofBijective (prefixPhysicalInput (P := 16) hfit hdiag) (fwSeedPhysicalInput_bijective n)
  have he : e.symm ((j, prefixOrdinaryPairIndex hfit (0, k, edge)), side) =
      Sum.inr (Sum.inl (finProdFinEquiv (j, k), (edge, side))) := by
    apply e.symm_apply_eq.mpr
    simpa [e, prefixPhysicalInput] using (prefixStageLayer_networkInput hfit rfl 0 j k edge side).symm
  change btGrowingOffsetCells (5 * (4 * 6)) hseed hs choice sr sc hsr hsc
    (e.symm ((j, prefixOrdinaryPairIndex hfit (0, k, edge)), side)) = _
  rw [he]
  exact prefixStageLayer_sequenceCell sr hsr j k edge side

/-- Actual ordinary column slot, in original (untransposed) square coordinates. -/
theorem fw_seed_existing_column_cell {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (j : Fin 16) (k : Fin 3) (edge : Fin n) (side : Bool) :
    fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      ((j, prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (1, k, edge)), side) =
    (LayerPacking.layerCell (prefixStageLayer sc hsc j k).1
      (prefixStageLayer sc hsc j k).2 (edge, side)).swap := by
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let e := Equiv.ofBijective (prefixPhysicalInput (P := 16) hfit hdiag) (fwSeedPhysicalInput_bijective n)
  have he : e.symm ((j, prefixOrdinaryPairIndex hfit (1, k, edge)), side) =
      Sum.inr (Sum.inr (finProdFinEquiv (j, k), (edge, side))) := by
    apply e.symm_apply_eq.mpr
    simpa [e, prefixPhysicalInput] using (prefixStageLayer_networkInput hfit rfl 1 j k edge side).symm
  change btGrowingOffsetCells (5 * (4 * 6)) hseed hs choice sr sc hsr hsc
    (e.symm ((j, prefixOrdinaryPairIndex hfit (1, k, edge)), side)) = _
  rw [he]
  exact congrArg Prod.swap (prefixStageLayer_sequenceCell sc hsc j k edge side)

/-- Model of the actual offset seed-pair incidence in a row. -/
noncomputable def fwSeedOffsetRowIncidence {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (j : Fin 16) (r : Fin n) : PrefixStagePair 6 3 n → ℝ
  | Sum.inl (rect, pair) => rectanglePairWeight hs choice (fun c => c.1 = r)
      (fwSeedRectangle hseed (finProdFinEquiv (j, rect)), pair)
  | Sum.inr (network, layer, edge) =>
      if network = 0 then
        LayerPacking.layerRowWeight (prefixStageLayer sr hsr j layer).1
          (prefixStageLayer sr hsr j layer).2 r edge
      else
        LayerPacking.layerColumnWeight (prefixStageLayer sc hsc j layer).1
          (prefixStageLayer sc hsc j layer).2 r edge

/-- Model of the actual offset seed-pair incidence in a column. -/
noncomputable def fwSeedOffsetColumnIncidence {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (j : Fin 16) (c : Fin n) : PrefixStagePair 6 3 n → ℝ
  | Sum.inl (rect, pair) => rectanglePairWeight hs choice (fun x => x.2 = c)
      (fwSeedRectangle hseed (finProdFinEquiv (j, rect)), pair)
  | Sum.inr (network, layer, edge) =>
      if network = 0 then
        LayerPacking.layerColumnWeight (prefixStageLayer sr hsr j layer).1
          (prefixStageLayer sr hsr j layer).2 c edge
      else
        LayerPacking.layerRowWeight (prefixStageLayer sc hsc j layer).1
          (prefixStageLayer sc hsc j layer).2 c edge

/-- Every labelled stage pair has its actual row incidence. -/
theorem fw_seed_existing_row_weight_at_label {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (j : Fin 16) (r : Fin n) (tag : PrefixStagePair 6 3 n) :
    physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
      (fun c => c.1 = r)
      (j, prefixStagePairSlot
        (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) tag) =
    fwSeedOffsetRowIncidence hseed hs choice sr sc hsr hsc j r tag := by
  classical
  cases tag with
  | inl x =>
    rcases x with ⟨rect, pair⟩
    simp only [prefixStagePairSlot, fwSeedOffsetRowIncidence]
    unfold physicalPairLineWeight rectanglePairWeight
    rw [fw_seed_existing_rectangle_cell hseed hs choice sr sc hsr hsc j rect pair false,
      fw_seed_existing_rectangle_cell hseed hs choice sr sc hsr hsc j rect pair true]
  | inr x =>
    rcases x with ⟨network, layer, edge⟩
    fin_cases network
    · simp [prefixStagePairSlot, fwSeedOffsetRowIncidence, physicalPairLineWeight,
        fw_seed_existing_row_cell, LayerPacking.layerRowWeight, LayerPacking.layerCell]
    · simp [prefixStagePairSlot, fwSeedOffsetRowIncidence, physicalPairLineWeight,
        fw_seed_existing_column_cell, LayerPacking.layerColumnWeight, LayerPacking.layerCell]

/-- Every labelled stage pair has its actual column incidence. -/
theorem fw_seed_existing_column_weight_at_label {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (j : Fin 16) (c : Fin n) (tag : PrefixStagePair 6 3 n) :
    physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
      (fun x => x.2 = c)
      (j, prefixStagePairSlot
        (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) tag) =
    fwSeedOffsetColumnIncidence hseed hs choice sr sc hsr hsc j c tag := by
  classical
  cases tag with
  | inl x =>
    rcases x with ⟨rect, pair⟩
    simp only [prefixStagePairSlot, fwSeedOffsetColumnIncidence]
    unfold physicalPairLineWeight rectanglePairWeight
    rw [fw_seed_existing_rectangle_cell hseed hs choice sr sc hsr hsc j rect pair false,
      fw_seed_existing_rectangle_cell hseed hs choice sr sc hsr hsc j rect pair true]
  | inr x =>
    rcases x with ⟨network, layer, edge⟩
    fin_cases network
    · simp [prefixStagePairSlot, fwSeedOffsetColumnIncidence, physicalPairLineWeight,
        fw_seed_existing_row_cell, LayerPacking.layerColumnWeight, LayerPacking.layerCell]
    · simp [prefixStagePairSlot, fwSeedOffsetColumnIncidence, physicalPairLineWeight,
        fw_seed_existing_column_cell, LayerPacking.layerRowWeight, LayerPacking.layerCell]

/-- Offset actual row incidence squares split into the physical rectangle
and ordinary network invoices. -/
theorem fw_seed_offset_row_incidence_sq_sum {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (j : Fin 16) (r : Fin n) :
    (∑ tag, (fwSeedOffsetRowIncidence hseed hs choice sr sc hsr hsc j r tag)^2) =
      fwSeedOffsetRectangleStageInvoice hseed hs choice (fun x => x.1 = r) j +
        physicalRowStageInvoice sr sc hsr hsc j r := by
  simp [fwSeedOffsetRowIncidence, fwSeedOffsetRectangleStageInvoice, physicalRowStageInvoice,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib]

/-- Offset actual column incidence squares split into the physical rectangle
and ordinary network invoices. -/
theorem fw_seed_offset_column_incidence_sq_sum {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (j : Fin 16) (c : Fin n) :
    (∑ tag, (fwSeedOffsetColumnIncidence hseed hs choice sr sc hsr hsc j c tag)^2) =
      fwSeedOffsetRectangleStageInvoice hseed hs choice (fun x => x.2 = c) j +
        physicalColumnStageInvoice sr sc hsr hsc j c := by
  simp [fwSeedOffsetColumnIncidence, fwSeedOffsetRectangleStageInvoice, physicalColumnStageInvoice,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib]


/-- Every actual row slot's squared incidence splits into the offset seed
rectangle invoice and the supplied ordinary network invoice. -/
theorem fw_seed_existing_row_squared_sum {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3) (j : Fin 16) (r : Fin n) :
    (∑ q : Fin (6 * (n + 8)),
      (physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun c => c ∈ rowCells r) (j, q)) ^ 2) =
      fwSeedOffsetRectangleStageInvoice hseed hs choice (fun c => c.1 = r) j +
        physicalRowStageInvoice sr sc hsr hsc j r := by
  classical
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let hexact : (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega
  let e := Equiv.ofBijective (prefixStagePairSlot hfit hdiag)
    (prefixStagePairSlot_bijective hfit hdiag hexact)
  let w := fun q : Fin (6 * (n + 8)) => physicalPairLineWeight
    (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) (fun c => c ∈ rowCells r) (j, q)
  calc
    ∑ q, w q ^ 2 = ∑ tag : PrefixStagePair 6 3 n, w (e tag) ^ 2 :=
      (e.sum_comp (fun q => w q ^ 2)).symm
    _ = _ := by
      simp only [w, e, Equiv.ofBijective_apply, mem_rowCells,
        fw_seed_existing_row_weight_at_label hseed hs choice sr sc hsr hsc j r]
      exact fw_seed_offset_row_incidence_sq_sum hseed hs choice sr sc hsr hsc j r

/-- The corresponding split for actual column slots. -/
theorem fw_seed_existing_column_squared_sum {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3) (j : Fin 16) (c : Fin n) :
    (∑ q : Fin (6 * (n + 8)),
      (physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun x => x ∈ columnCells c) (j, q)) ^ 2) =
      fwSeedOffsetRectangleStageInvoice hseed hs choice (fun x => x.2 = c) j +
        physicalColumnStageInvoice sr sc hsr hsc j c := by
  classical
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let hexact : (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega
  let e := Equiv.ofBijective (prefixStagePairSlot hfit hdiag)
    (prefixStagePairSlot_bijective hfit hdiag hexact)
  let w := fun q : Fin (6 * (n + 8)) => physicalPairLineWeight
    (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) (fun x => x ∈ columnCells c) (j, q)
  calc
    ∑ q, w q ^ 2 = ∑ tag : PrefixStagePair 6 3 n, w (e tag) ^ 2 :=
      (e.sum_comp (fun q => w q ^ 2)).symm
    _ = _ := by
      simp only [w, e, Equiv.ofBijective_apply, mem_columnCells,
        fw_seed_existing_column_weight_at_label hseed hs choice sr sc hsr hsc j c]
      exact fw_seed_offset_column_incidence_sq_sum hseed hs choice sr sc hsr hsc j c

/-- The actual row-pair incidence obeys the source-form width invoice for a
packed row-layer family. This assumes the supplied per-stage width cap. -/
theorem fw_seed_existing_row_weighted_invoice {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3) (reservedRows : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows sr) (r : Fin n)
    (width : Fin 16 → ℝ) (z : ℝ) (hwidth : ∀ j, (width j) ^ 2 ≤ z ^ 2) :
    (∑ j, (width j) ^ 2 * ∑ q : Fin (6 * (n + 8)),
      (physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun c => c ∈ rowCells r) (j, q)) ^ 2) ≤
      18 * (∑ j, (width j) ^ 2) + 4 * z ^ 2 := by
  simp_rw [fw_seed_existing_row_squared_sum hseed hs choice sr sc hsr hsc]
  have hord : ∀ j, physicalRowStageInvoice sr sc hsr hsc j r ≤ 18 := by
    intro j
    have h := physicalRowStageInvoice_eq (by decide : 6 = 2 * 3)
      sr sc hsr hsc reservedRows packedRows j r
    norm_num at h
    exact le_of_eq h
  simpa [add_comm] using fw_seed_offset_row_combined_width_invoice hseed hs choice r
    width (fun j => physicalRowStageInvoice sr sc hsr hsc j r) z hord hwidth

/-- The corresponding width invoice for a packed column-layer family. -/
theorem fw_seed_existing_column_weighted_invoice {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3) (reservedCols : Finset (Cell n))
    (packedCols : LayerPacking.PackedLayers reservedCols sc) (c : Fin n)
    (width : Fin 16 → ℝ) (z : ℝ) (hwidth : ∀ j, (width j) ^ 2 ≤ z ^ 2) :
    (∑ j, (width j) ^ 2 * ∑ q : Fin (6 * (n + 8)),
      (physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun x => x ∈ columnCells c) (j, q)) ^ 2) ≤
      18 * (∑ j, (width j) ^ 2) + 4 * z ^ 2 := by
  simp_rw [fw_seed_existing_column_squared_sum hseed hs choice sr sc hsr hsc]
  have hord : ∀ j, physicalColumnStageInvoice sr sc hsr hsc j c ≤ 18 := by
    intro j
    have h := physicalColumnStageInvoice_eq (by decide : 6 = 2 * 3)
      sr sc hsr hsc reservedCols packedCols j c
    norm_num at h
    exact le_of_eq h
  simpa [add_comm] using fw_seed_offset_column_combined_width_invoice hseed hs choice c
    width (fun j => physicalColumnStageInvoice sr sc hsr hsc j c) z hord hwidth

end
end Sude
