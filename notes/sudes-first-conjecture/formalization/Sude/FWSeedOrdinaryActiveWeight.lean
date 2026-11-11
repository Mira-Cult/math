import Sude.FWOrdinaryRectangleExclusion
import Sude.FWSeedLineIncidence

/-! Exact seed ordinary incidences relative to the actual active rectangle
support of the packed FW layout. No line discrepancy or numerical gate is
asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

/-- All endpoints of a seed rectangle pair are in the active support. -/
theorem fw_seed_rectangle_cell_in_active {n P : ℕ} (hP : P ≤ 238)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (j : Fin 16) (rect : Fin (4 * 6)) (pair : Fin 2) (side : Bool) :
    fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      ((j, prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect,pair)),side) ∈
      activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP) := by
  classical
  rw [fw_seed_existing_rectangle_cell]
  apply Finset.mem_image.mpr
  refine ⟨(fwSeedRectangle hseed (finProdFinEquiv (j,rect)), prefixPairCorner pair side), ?_, rfl⟩
  apply Finset.mem_product.mpr
  refine ⟨?_, Finset.mem_univ _⟩
  rw [fw_active_rectangle_label_mem_iff]
  have ht := (finProdFinEquiv (j,rect) : Fin (16 * (4 * 6))).isLt
  dsimp [fwSeedRectangle, fwActiveRectangleCount]
  omega

/-- Seed ordinary endpoints avoid the active rectangle support. -/
theorem fw_seed_ordinary_cell_off_active {n P : ℕ} (hP : P ≤ 238)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (j : Fin 16) (network : Fin 2) (k : Fin 3) (edge : Fin n) (side : Bool) :
    fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      ((j, prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (network,k,edge)), side) ∉ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP) := by
  have hsub := active_rectangle_support_subset_packed hs choice (fwActiveRectangleLabels n P hP)
  fin_cases network
  · change fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j, prefixOrdinaryPairIndex (by omega) (0,k,edge)), side) ∉ _
    rw [fw_seed_existing_row_cell]
    have h := fw_selected_stage_layer_off_reserved hrows (selected := sr)
      (by intro x hx; simp [hx]) hsr j k edge side
    exact fun hx => h (hsub hx)
  · change fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j, prefixOrdinaryPairIndex (by omega) (1,k,edge)), side) ∉ _
    rw [fw_seed_existing_column_cell]
    have h := fw_selected_stage_layer_swap_off_reserved hcols (selected := sc)
      (by intro x hx; simp [hx]) hsc j k edge side
    exact fun hx => h (Finset.mem_union_left _ (hsub hx))

/-- On each seed stage the active-rectangle restricted pair weight is exactly
its rectangle component, on any supplied physical line predicate. -/
theorem fw_seed_active_rectangle_weight {n P : ℕ} (hP : P ≤ 238)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (line : Cell n → Prop) [DecidablePred line] (j : Fin 16) :
    (∑ q : Fin (6 * (n + 8)), physicalPairLineWeight
      (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
      (fun z => z ∈ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP) ∧ line z) (j,q)) =
      fwSeedRectangleStageLineWeight hseed hs choice line j := by
  classical
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let hexact : (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega
  let e := Equiv.ofBijective (prefixStagePairSlot hfit hdiag)
    (prefixStagePairSlot_bijective hfit hdiag hexact)
  let w := fun q : Fin (6 * (n + 8)) => physicalPairLineWeight
    (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
    (fun z => z ∈ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP) ∧ line z) (j,q)
  calc
    ∑ q, w q = ∑ tag : PrefixStagePair 6 3 n, w (e tag) := (e.sum_comp w).symm
    _ = _ := by
      have hrectsum : (∑ tag : Fin (4 * 6) × Fin 2, w (e (Sum.inl tag))) =
          fwSeedRectangleStageLineWeight hseed hs choice line j := by
        rw [Fintype.sum_prod_type]
        unfold fwSeedRectangleStageLineWeight
        apply Finset.sum_congr rfl
        intro rect _
        apply Finset.sum_congr rfl
        intro pair _
        dsimp [w, e, prefixStagePairSlot]
        unfold physicalPairLineWeight rectanglePairWeight
        rw [fw_seed_existing_rectangle_cell hseed hs choice sr sc hsr hsc j rect pair false,
          fw_seed_existing_rectangle_cell hseed hs choice sr sc hsr hsc j rect pair true]
        have hf := fw_seed_rectangle_cell_in_active hP hseed hs choice sr sc hsr hsc j rect pair false
        have ht := fw_seed_rectangle_cell_in_active hP hseed hs choice sr sc hsr hsc j rect pair true
        rw [fw_seed_existing_rectangle_cell] at hf ht
        simp [hf, ht]
        split_ifs <;> simp_all
      have hordsum : (∑ tag : Fin 2 × Fin 3 × Fin n, w (e (Sum.inr tag))) = 0 := by
        apply Finset.sum_eq_zero
        intro tag _
        rcases tag with ⟨network,k,edge⟩
        dsimp [w, e, prefixStagePairSlot]
        unfold physicalPairLineWeight
        have hf := fw_seed_ordinary_cell_off_active hP hseed hs choice br bc sr sc wr wc gr gc hsr hsc hrows hcols j network k edge false
        have ht := fw_seed_ordinary_cell_off_active hP hseed hs choice br bc sr sc wr wc gr gc hsr hsc hrows hcols j network k edge true
        simp [hf, ht]
      rw [Fintype.sum_sum_type, hrectsum, hordsum, add_zero]

/-- At every seed stage, removing active-rectangle incidence leaves exactly
twelve ordinary physical entries on every row and column. -/
theorem fw_seed_ordinary_active_mass {n P : ℕ} (hP : P ≤ 238)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (j : Fin 16) :
    (∀ r : Fin n,
      (∑ q : Fin (6 * (n + 8)), physicalPairLineWeight
        (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) (fun z => z.1 = r) (j,q)) -
      (∑ q : Fin (6 * (n + 8)), physicalPairLineWeight
        (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun z => z ∈ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP) ∧ z.1 = r) (j,q)) = 12) ∧
    (∀ c : Fin n,
      (∑ q : Fin (6 * (n + 8)), physicalPairLineWeight
        (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) (fun z => z.2 = c) (j,q)) -
      (∑ q : Fin (6 * (n + 8)), physicalPairLineWeight
        (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun z => z ∈ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP) ∧ z.2 = c) (j,q)) = 12) := by
  classical
  constructor
  · intro r
    have h := fw_seed_existing_row_line_weight hseed hs choice sr sc hsr hsc j r
    have hrect := fw_seed_active_rectangle_weight hP hseed hs choice br bc sr sc wr wc gr gc hsr hsc hrows hcols (fun z => z.1 = r) j
    linarith
  · intro c
    have h := fw_seed_existing_column_line_weight hseed hs choice sr sc hsr hsc j c
    have hrect := fw_seed_active_rectangle_weight hP hseed hs choice br bc sr sc wr wc gr gc hsr hsc hrows hcols (fun z => z.2 = c) j
    linarith

end
end Sude
