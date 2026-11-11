import Sude.FWJointPhysicalGaps
import Sude.FWSeedOffsetActualRowColumn
import Sude.FWSeedReallocationRolePreservation
namespace Sude
noncomputable section

theorem fw_row_oriented_of_preserved_cells {n : ℕ}
    (grown b : Cell n ≃ Fin (n*n)) (layers : List (LayerPacking.Layer n))
    (h : fwRowsOriented grown layers)
    (hsame : ∀ (i : Fin layers.length) (e : Fin n) (side : Bool),
      entry b (LayerPacking.sequenceCell layers (i, (e, side))) =
      entry grown (LayerPacking.sequenceCell layers (i, (e, side)))) :
    fwRowsOriented b layers := by
  intro i e
  have hl := hsame i e false
  have hh := hsame i e true
  simp only [LayerPacking.sequenceCell, LayerPacking.layerCell, Bool.false_eq_true, ↓reduceIte] at hl hh
  rw [hl, hh]
  exact h i e

theorem fw_column_oriented_of_preserved_cells {n : ℕ}
    (grown b : Cell n ≃ Fin (n*n)) (layers : List (LayerPacking.Layer n))
    (h : fwColumnsOriented grown layers)
    (hsame : ∀ (i : Fin layers.length) (e : Fin n) (side : Bool),
      entry b (LayerPacking.sequenceCell layers (i, (e, side))).swap =
      entry grown (LayerPacking.sequenceCell layers (i, (e, side))).swap) :
    fwColumnsOriented b layers := by
  intro i e
  have hl := hsame i e false
  have hh := hsame i e true
  simp only [LayerPacking.sequenceCell, LayerPacking.layerCell, Bool.false_eq_true, ↓reduceIte, Prod.swap_prod_mk] at hl hh
  rw [hl, hh]
  exact h i e

theorem fw_joint_equations_of_preserved_families {n : ℕ}
    (grown b : Cell n ≃ Fin (n*n))
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : fwRowsOriented grown br) (hbc : fwColumnsOriented grown bc)
    (hwr : fwRowsOriented grown wr) (hwc : fwColumnsOriented grown wc)
    (hgr : fwRowsOriented grown gr) (hgc : fwColumnsOriented grown gc)
    (hsr : fwRowsOriented b sr) (hsc : fwColumnsOriented b sc)
    (hbrfix : ∀ (i : Fin br.length) (e : Fin n) (side : Bool),
      entry b (LayerPacking.sequenceCell br (i, (e, side))) = entry grown (LayerPacking.sequenceCell br (i, (e, side))))
    (hbcfix : ∀ (i : Fin bc.length) (e : Fin n) (side : Bool),
      entry b (LayerPacking.sequenceCell bc (i, (e, side))).swap = entry grown (LayerPacking.sequenceCell bc (i, (e, side))).swap)
    (hwrfix : ∀ (i : Fin wr.length) (e : Fin n) (side : Bool),
      entry b (LayerPacking.sequenceCell wr (i, (e, side))) = entry grown (LayerPacking.sequenceCell wr (i, (e, side))))
    (hwcfix : ∀ (i : Fin wc.length) (e : Fin n) (side : Bool),
      entry b (LayerPacking.sequenceCell wc (i, (e, side))).swap = entry grown (LayerPacking.sequenceCell wc (i, (e, side))).swap)
    (hgrfix : ∀ (i : Fin gr.length) (e : Fin n) (side : Bool),
      entry b (LayerPacking.sequenceCell gr (i, (e, side))) = entry grown (LayerPacking.sequenceCell gr (i, (e, side))))
    (hgcfix : ∀ (i : Fin gc.length) (e : Fin n) (side : Bool),
      entry b (LayerPacking.sequenceCell gc (i, (e, side))).swap = entry grown (LayerPacking.sequenceCell gc (i, (e, side))).swap) :
    let rows := ((br ++ sr) ++ wr) ++ gr
    let cols := ((bc ++ sc) ++ wc) ++ gc
    (∀ i e, entry b ((rows.get i).1 e, (rows.get i).2 e) =
      entry b (e, (rows.get i).2 e) + fwPhysicalRowLayerGap b rows i e) ∧
    (∀ i e, entry b ((cols.get i).2 e, (cols.get i).1 e) =
      entry b ((cols.get i).2 e, e) + fwPhysicalColumnLayerGap b cols i e) := by
  exact fw_four_family_physical_gap_equations b br bc sr sc wr wc gr gc
    (fw_row_oriented_of_preserved_cells grown b br hbr hbrfix)
    (fw_column_oriented_of_preserved_cells grown b bc hbc hbcfix)
    hsr hsc
    (fw_row_oriented_of_preserved_cells grown b wr hwr hwrfix)
    (fw_column_oriented_of_preserved_cells grown b wc hwc hwcfix)
    (fw_row_oriented_of_preserved_cells grown b gr hgr hgrfix)
    (fw_column_oriented_of_preserved_cells grown b gc hgc hgcfix)
theorem fw_reallocated_seed_family_orientations {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (b : Cell n ≃ Fin (n*n))
    (hgap : ∀ j i, entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),true)) =
      entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),false)) + 2) :
    fwRowsOriented b sr ∧ fwColumnsOriented b sc := by
  constructor
  · intro i e
    let jk : Fin 16 × Fin 3 := finProdFinEquiv.symm (Fin.cast hsr i)
    have hi : bridgeStageLayerIndex hsr jk.1 jk.2 = i := by
      change Fin.cast _ (finProdFinEquiv (finProdFinEquiv.symm (Fin.cast _ i))) = i
      simp
    have hr := hgap jk.1 (prefixOrdinaryPairIndex
      (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (0,jk.2,e))
    rw [fw_seed_existing_row_cell, fw_seed_existing_row_cell] at hr
    change entry b ((sr.get (bridgeStageLayerIndex hsr jk.1 jk.2)).1 e, (sr.get (bridgeStageLayerIndex hsr jk.1 jk.2)).2 e) =
      entry b (e, (sr.get (bridgeStageLayerIndex hsr jk.1 jk.2)).2 e) + 2 at hr
    rw [hi] at hr
    omega
  · intro i e
    let jk : Fin 16 × Fin 3 := finProdFinEquiv.symm (Fin.cast hsc i)
    have hi : bridgeStageLayerIndex hsc jk.1 jk.2 = i := by
      change Fin.cast _ (finProdFinEquiv (finProdFinEquiv.symm (Fin.cast _ i))) = i
      simp
    have hc := hgap jk.1 (prefixOrdinaryPairIndex
      (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (1,jk.2,e))
    rw [fw_seed_existing_column_cell, fw_seed_existing_column_cell] at hc
    change entry b ((sc.get (bridgeStageLayerIndex hsc jk.1 jk.2)).2 e, (sc.get (bridgeStageLayerIndex hsc jk.1 jk.2)).1 e) =
      entry b ((sc.get (bridgeStageLayerIndex hsc jk.1 jk.2)).2 e, e) + 2 at hc
    rw [hi] at hc
    omega

theorem fw_bridge_preserved_layer_entries {n : ℕ}
    (br bc : List (LayerPacking.Layer n)) (hr : br.length = 5*3) (hc : bc.length = 5*3)
    (grown b : Cell n ≃ Fin (n*n))
    (hbridge : ∀ x, entry b (fwBridgeLayerCells br bc hr hc x) = entry grown (fwBridgeLayerCells br bc hr hc x)) :
    (∀ (i : Fin br.length) (e : Fin n) (side : Bool),
      entry b (LayerPacking.sequenceCell br (i, (e, side))) = entry grown (LayerPacking.sequenceCell br (i, (e, side)))) ∧
    (∀ (i : Fin bc.length) (e : Fin n) (side : Bool),
      entry b (LayerPacking.sequenceCell bc (i, (e, side))).swap = entry grown (LayerPacking.sequenceCell bc (i, (e, side))).swap) := by
  constructor
  · intro i e side
    let t : Fin 5 × Fin 3 := finProdFinEquiv.symm (Fin.cast hr i)
    have hi : Fin.cast hr.symm (finProdFinEquiv t) = i := by
      change Fin.cast hr.symm (finProdFinEquiv (finProdFinEquiv.symm (Fin.cast hr i))) = i
      rw [Equiv.apply_symm_apply]
      simp
    have h := hbridge ((t.1, (t.2, e)), (false, side))
    simpa [fwBridgeLayerCells, fwBridgeLayerIndex, hi] using h
  · intro i e side
    let t : Fin 5 × Fin 3 := finProdFinEquiv.symm (Fin.cast hc i)
    have hi : Fin.cast hc.symm (finProdFinEquiv t) = i := by
      change Fin.cast hc.symm (finProdFinEquiv (finProdFinEquiv.symm (Fin.cast hc i))) = i
      rw [Equiv.apply_symm_apply]
      simp
    have h := hbridge ((t.1, (t.2, e)), (true, side))
    simpa [fwBridgeLayerCells, fwBridgeLayerIndex, hi] using h

theorem fw_wide_preserved_layer_entries {n L : ℕ}
    (hwide : 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6) ≤ L)
    (hs : 2*L+1 ≤ n) (choice : Fin L → Bool)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3*(n/450))*3)
    (hwc : wc.length = (3*(n/450))*3) (grown b : Cell n ≃ Fin (n*n))
    (hwidefix : ∀ x : FWWideInputs n, entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) = entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x)) :
    (∀ (i : Fin wr.length) (e : Fin n) (side : Bool),
      entry b (LayerPacking.sequenceCell wr (i, (e, side))) = entry grown (LayerPacking.sequenceCell wr (i, (e, side)))) ∧
    (∀ (i : Fin wc.length) (e : Fin n) (side : Bool),
      entry b (LayerPacking.sequenceCell wc (i, (e, side))).swap = entry grown (LayerPacking.sequenceCell wc (i, (e, side))).swap) := by
  constructor
  · intro i e side
    let t : Fin (3*(n/450)) × Fin 3 := finProdFinEquiv.symm (Fin.cast hwr i)
    have hi : Fin.cast hwr.symm (finProdFinEquiv t) = i := by
      change Fin.cast hwr.symm (finProdFinEquiv (finProdFinEquiv.symm (Fin.cast hwr i))) = i
      rw [Equiv.apply_symm_apply]
      simp
    have h := hwidefix (Sum.inr ((t.1, (t.2, e)), (false, side)))
    simpa [fwWidePhysicalCells, fwWideOrdinaryCells, fwWideLayerIndex, hi] using h
  · intro i e side
    let t : Fin (3*(n/450)) × Fin 3 := finProdFinEquiv.symm (Fin.cast hwc i)
    have hi : Fin.cast hwc.symm (finProdFinEquiv t) = i := by
      change Fin.cast hwc.symm (finProdFinEquiv (finProdFinEquiv.symm (Fin.cast hwc i))) = i
      rw [Equiv.apply_symm_apply]
      simp
    have h := hwidefix (Sum.inr ((t.1, (t.2, e)), (true, side)))
    simpa [fwWidePhysicalCells, fwWideOrdinaryCells, fwWideLayerIndex, hi] using h

theorem fw_growth_preserved_layer_entries {n L P : ℕ}
    (offset : ℕ) (hoff : offset + P * (4*6) ≤ L)
    (hs : 2*L+1 ≤ n) (choice : Fin L → Bool)
    (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = P*3) (hgc : gc.length = P*3)
    (grown b : Cell n ≃ Fin (n*n))
    (hfix : ∀ x : PrefixPhysicalInputs P 6 3 n,
      entry b (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x) =
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x)) :
    (∀ (i : Fin gr.length) (e : Fin n) (side : Bool),
      entry b (LayerPacking.sequenceCell gr (i, (e, side))) = entry grown (LayerPacking.sequenceCell gr (i, (e, side)))) ∧
    (∀ (i : Fin gc.length) (e : Fin n) (side : Bool),
      entry b (LayerPacking.sequenceCell gc (i, (e, side))).swap = entry grown (LayerPacking.sequenceCell gc (i, (e, side))).swap) := by
  constructor
  · intro i e side
    have h := hfix (Sum.inr (Sum.inl (Fin.cast hgr i, (e,side))))
    simpa [btGrowingOffsetCells] using h
  · intro i e side
    have h := hfix (Sum.inr (Sum.inr (Fin.cast hgc i, (e,side))))
    simpa [btGrowingOffsetCells] using h

/-- Seed gap-two equations and preservation of all other physical roles
reconstruct the four-family joint row and column orientations. -/
theorem fw_joint_gap_equations_after_seed_reallocation {n L P : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (offset : ℕ) (hoff : offset + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (grown b : Cell n ≃ Fin (n*n))
    (hbr : fwRowsOriented grown br) (hbc : fwColumnsOriented grown bc)
    (hwrO : fwRowsOriented grown wr) (hwcO : fwColumnsOriented grown wc)
    (hgrO : fwRowsOriented grown gr) (hgcO : fwColumnsOriented grown gc)
    (hseedgap : ∀ j i, entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),true)) =
      entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),false)) + 2)
    (hbridge : ∀ x, entry b (fwBridgeLayerCells br bc hr hc x) = entry grown (fwBridgeLayerCells br bc hr hc x))
    (hwidefix : ∀ x : FWWideInputs n, entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x))
    (hgrowth : ∀ x : PrefixPhysicalInputs P 6 3 n,
      entry b (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x) =
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x)) :
    let rows := ((br ++ sr) ++ wr) ++ gr
    let cols := ((bc ++ sc) ++ wc) ++ gc
    (∀ i e, entry b ((rows.get i).1 e, (rows.get i).2 e) =
      entry b (e, (rows.get i).2 e) + fwPhysicalRowLayerGap b rows i e) ∧
    (∀ i e, entry b ((cols.get i).2 e, (cols.get i).1 e) =
      entry b ((cols.get i).2 e, e) + fwPhysicalColumnLayerGap b cols i e) := by
  obtain ⟨hsrO, hscO⟩ := fw_reallocated_seed_family_orientations hseed hs choice sr sc hsr hsc b hseedgap
  obtain ⟨hbrfix, hbcfix⟩ := fw_bridge_preserved_layer_entries br bc hr hc grown b hbridge
  obtain ⟨hwrfix, hwcfix⟩ := fw_wide_preserved_layer_entries hwide hs choice wr wc hwr hwc grown b hwidefix
  obtain ⟨hgrfix, hgcfix⟩ := fw_growth_preserved_layer_entries offset hoff hs choice gr gc hgr hgc grown b hgrowth
  exact fw_joint_equations_of_preserved_families grown b br bc sr sc wr wc gr gc
    hbr hbc hwrO hwcO hgrO hgcO hsrO hscO hbrfix hbcfix hwrfix hwcfix hgrfix hgcfix

theorem fw_rows_oriented_of_gap_equations {n : ℕ} (a : Cell n ≃ Fin (n*n))
    (layers : List (LayerPacking.Layer n))
    (h : ∀ i e, entry a ((layers.get i).1 e, (layers.get i).2 e) =
      entry a (e, (layers.get i).2 e) + fwPhysicalRowLayerGap a layers i e) :
    fwRowsOriented a layers := by
  intro i e
  have hh := h i e
  omega

theorem fw_columns_oriented_of_gap_equations {n : ℕ} (a : Cell n ≃ Fin (n*n))
    (layers : List (LayerPacking.Layer n))
    (h : ∀ i e, entry a ((layers.get i).2 e, (layers.get i).1 e) =
      entry a ((layers.get i).2 e, e) + fwPhysicalColumnLayerGap a layers i e) :
    fwColumnsOriented a layers := by
  intro i e
  have hh := h i e
  omega

theorem fw_rows_oriented_of_membership {n : ℕ} (a : Cell n ≃ Fin (n*n))
    (small all : List (LayerPacking.Layer n))
    (hmem : ∀ x ∈ small, x ∈ all) (h : fwRowsOriented a all) :
    fwRowsOriented a small := by
  intro i e
  have hm := hmem (small.get i) (List.get_mem small i)
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
  simpa only [hj] using h j e

theorem fw_columns_oriented_of_membership {n : ℕ} (a : Cell n ≃ Fin (n*n))
    (small all : List (LayerPacking.Layer n))
    (hmem : ∀ x ∈ small, x ∈ all) (h : fwColumnsOriented a all) :
    fwColumnsOriented a small := by
  intro i e
  have hm := hmem (small.get i) (List.get_mem small i)
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
  simpa only [hj] using h j e

theorem fw_joint_gap_equations_after_seed_reallocation_of_joint_gaps {n L P : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (offset : ℕ) (hoff : offset + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (grown b : Cell n ≃ Fin (n*n))
    (hrow : ∀ i e, entry grown (((((br ++ sr) ++ wr) ++ gr).get i).1 e, ((((br ++ sr) ++ wr) ++ gr).get i).2 e) =
      entry grown (e, ((((br ++ sr) ++ wr) ++ gr).get i).2 e) + fwPhysicalRowLayerGap grown (((br ++ sr) ++ wr) ++ gr) i e)
    (hcol : ∀ i e, entry grown (((((bc ++ sc) ++ wc) ++ gc).get i).2 e, ((((bc ++ sc) ++ wc) ++ gc).get i).1 e) =
      entry grown (((((bc ++ sc) ++ wc) ++ gc).get i).2 e, e) + fwPhysicalColumnLayerGap grown (((bc ++ sc) ++ wc) ++ gc) i e)
    (hseedgap : ∀ j i, entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),true)) =
      entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),false)) + 2)
    (hbridge : ∀ x, entry b (fwBridgeLayerCells br bc hr hc x) = entry grown (fwBridgeLayerCells br bc hr hc x))
    (hwidefix : ∀ x : FWWideInputs n, entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x))
    (hgrowth : ∀ x : PrefixPhysicalInputs P 6 3 n,
      entry b (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x) =
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x)) :
    let rows := ((br ++ sr) ++ wr) ++ gr
    let cols := ((bc ++ sc) ++ wc) ++ gc
    (∀ i e, entry b ((rows.get i).1 e, (rows.get i).2 e) =
      entry b (e, (rows.get i).2 e) + fwPhysicalRowLayerGap b rows i e) ∧
    (∀ i e, entry b ((cols.get i).2 e, (cols.get i).1 e) =
      entry b ((cols.get i).2 e, e) + fwPhysicalColumnLayerGap b cols i e) := by
  have hrows := fw_rows_oriented_of_gap_equations grown (((br ++ sr) ++ wr) ++ gr) hrow
  have hcols := fw_columns_oriented_of_gap_equations grown (((bc ++ sc) ++ wc) ++ gc) hcol
  have hbr := fw_rows_oriented_of_membership grown br _ (by intro x hx; simp [List.mem_append, hx]) hrows
  have hbc := fw_columns_oriented_of_membership grown bc _ (by intro x hx; simp [List.mem_append, hx]) hcols
  have hwrO := fw_rows_oriented_of_membership grown wr _ (by intro x hx; simp [List.mem_append, hx]) hrows
  have hwcO := fw_columns_oriented_of_membership grown wc _ (by intro x hx; simp [List.mem_append, hx]) hcols
  have hgrO := fw_rows_oriented_of_membership grown gr _ (by intro x hx; simp [List.mem_append, hx]) hrows
  have hgcO := fw_columns_oriented_of_membership grown gc _ (by intro x hx; simp [List.mem_append, hx]) hcols
  exact fw_joint_gap_equations_after_seed_reallocation hseed hwide offset hoff hs choice
    br bc sr sc wr wc gr gc hr hc hsr hsc hwr hwc hgr hgc grown b
    hbr hbc hwrO hwcO hgrO hgcO hseedgap hbridge hwidefix hgrowth

end
end Sude
