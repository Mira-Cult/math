import Sude.FC2KRoleSelection
import Sude.FC2KCentralCompletion
import Sude.PrefixInstalledNetwork
import Sude.PermutationExceptions
import Sude.PhysicalCutRouting
import Sude.ActiveRectangleDiagonalGeometry
import Sude.FTTTargetList

/-!
# FC2K Joint Physical Installation & Central Completion (`FC2KJointInstallation`)

Given a verified `FC2KSelectedRoles` package, jointly installs:
1. All `L = 24 * P + 24 * J + 2 * W_diag` diagonal rectangles via RP1 (`packedRectangleCorner`).
2. Both `3 * (P + J + W_ord)` expanding ordinary permutation-layer networks (`rows`, `cols`).
3. Sharp central-band diagonal and off-diagonal completion (`fc2k_central_band_sharp_completion_two_budgets`),
   producing a completed pool bijection `c : Cell n ≃ Fin (n * n)`, both `CenteredNetwork`s `BR, BC`
   on `c`, the diagonal midpoint difference bound `hmain_diff_c`, and the exact row/column ideal
   mean-conserving decomposition `M_row_ideal`, `M_col_ideal` with pairwise width bounds.
-/

namespace Sude

noncomputable section

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Parity-alternating diagonal designation `decide (t.val % 2 = 0)` on `Fin L`. -/
def fc2kDiagChoice (L : ℕ) (t : Fin L) : Bool :=
  decide (t.val % 2 = 0)

/-- Exact `K`-vs-`K` balance of `fc2kDiagChoice (2 * K)` across `true` and `false`. -/
theorem fc2kDiagChoice_balance (K : ℕ) :
    ((Finset.univ : Finset (Fin (2 * K))).filter
      (fun t => fc2kDiagChoice (2 * K) t = true)).card = K ∧
    ((Finset.univ : Finset (Fin (2 * K))).filter
      (fun t => fc2kDiagChoice (2 * K) t = false)).card = K := by
  let fEven (q : Fin K) : Fin (2 * K) := ⟨2 * q.val, by omega⟩
  let fOdd (q : Fin K) : Fin (2 * K) := ⟨2 * q.val + 1, by omega⟩
  have hfE : Function.Injective fEven := fun a b h =>
    Fin.ext (by have hv := congrArg Fin.val h; dsimp [fEven] at hv; omega)
  have hfO : Function.Injective fOdd := fun a b h =>
    Fin.ext (by have hv := congrArg Fin.val h; dsimp [fOdd] at hv; omega)
  have hsetE : (Finset.univ : Finset (Fin (2 * K))).filter
      (fun t => fc2kDiagChoice (2 * K) t = true) = Finset.univ.image fEven := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, fc2kDiagChoice,
      decide_eq_true_eq, Finset.mem_image]
    exact ⟨fun h => ⟨⟨t.val / 2, by omega⟩, Fin.ext (by dsimp [fEven]; omega)⟩,
      fun ⟨q, hq⟩ => by rw [← hq]; dsimp [fEven]; omega⟩
  have hsetO : (Finset.univ : Finset (Fin (2 * K))).filter
      (fun t => fc2kDiagChoice (2 * K) t = false) = Finset.univ.image fOdd := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, fc2kDiagChoice,
      decide_eq_false_iff_not, Finset.mem_image]
    exact ⟨fun h => ⟨⟨t.val / 2, by omega⟩, Fin.ext (by dsimp [fOdd]; omega)⟩,
      fun ⟨q, hq⟩ => by rw [← hq]; dsimp [fOdd]; omega⟩
  rw [hsetE, hsetO, Finset.card_image_of_injective _ hfE, Finset.card_image_of_injective _ hfO]
  simp

/-- Accumulated `layersSupport` equals the image of `sequenceCell`. -/
theorem layersSupport_eq_image_sequenceCell {n : ℕ} (layers : List (LayerPacking.Layer n)) :
    LayerPacking.layersSupport layers = Finset.univ.image (LayerPacking.sequenceCell layers) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun hz => LayerPacking.sequenceCell_covers layers z hz,
    fun ⟨x, hx⟩ => hx ▸ LayerPacking.layerSupport_subset (layers.get x.1) layers
      (List.get_mem layers x.1) (LayerPacking.sequenceCell_mem layers x.1 x.2)⟩

/-- Transposed `layersSupport` equals the image of `(sequenceCell layers ·).swap`. -/
theorem transposeCells_layersSupport_eq_image {n : ℕ} (layers : List (LayerPacking.Layer n)) :
    LayerPacking.transposeCells (LayerPacking.layersSupport layers) =
      Finset.univ.image (fun x => (LayerPacking.sequenceCell layers x).swap) := by
  rw [LayerPacking.transposeCells, layersSupport_eq_image_sequenceCell, Finset.image_image]
  rfl

/-- Exact cardinality of `layersSupport` and `transposeCells (layersSupport)` for `PackedLayers`. -/
theorem packedLayers_support_cards {n : ℕ} {res₁ res₂ : Finset (Cell n)}
    {rows cols : List (LayerPacking.Layer n)}
    (hr : LayerPacking.PackedLayers res₁ rows)
    (hc : LayerPacking.PackedLayers res₂ cols) :
    (LayerPacking.layersSupport rows).card = 2 * n * rows.length ∧
    (LayerPacking.transposeCells (LayerPacking.layersSupport cols)).card = 2 * n * cols.length := by
  have hc_inj : Function.Injective (fun x => (LayerPacking.sequenceCell cols x).swap) :=
    Prod.swap_injective.comp hc.sequenceCell_injective
  rw [layersSupport_eq_image_sequenceCell rows, transposeCells_layersSupport_eq_image cols,
    Finset.card_image_of_injective _ hr.sequenceCell_injective,
    Finset.card_image_of_injective _ hc_inj]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  exact ⟨by ring, by ring⟩

/-- Construct a `CenteredNetwork` on any `RowNetworkPairs` indexed by `Fin layers.length × Fin n`
when `layers.length = S * 3` and `layers.map Prod.fst = bridgeRepeatedPermutations S p`. -/
def fc2kInstalledCenteredNetwork {S n : ℕ} {a : Cell n ≃ Fin (n * n)}
    (layers : List (LayerPacking.Layer n)) (hS : layers.length = S * 3)
    (p : Fin 3 → Equiv.Perm (Fin n))
    (hperms : layers.map Prod.fst = bridgeRepeatedPermutations S p)
    (v : RowNetworkPairs (Fin layers.length × Fin n) a)
    (hv_low : ∀ k, v.low k = k.2)
    (hv_high : ∀ k, v.high k = (layers.get k.1).1 k.2)
    (edgeRadius : Fin 3 × Fin n → ℕ)
    (hgrid : ∀ e : Fin 3 × Fin n,
      CompleteEvenGrid (prefixPairBlock S (prefixPhysicalStageSlot hS) e) v.gap (edgeRadius e)) :
    CenteredNetwork (Fin 3 × Fin n) (Fin layers.length × Fin n) v where
  block := prefixPairBlock S (prefixPhysicalStageSlot hS)
  radius := edgeRadius
  source := Prod.snd
  target := fun e => p e.1 e.2
  disjoint := fun e f h => prefixPairBlock_disjoint S (prefixPhysicalStageSlot hS)
    (prefixPhysicalStageSlot_injective hS) e f h
  grid := hgrid
  endpoints := by
    intro e k hk
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨hv_low _, (hv_high _).trans (bridgeStageLayer_endpoints layers hS p hperms s e.1 e.2)⟩

/-- Column-pair sum bounds of a rectangle follow from row-pair sum bounds and equal gaps:
`2 * (s₀ + s₂) = (s₀ + s₁) + (s₃ + s₂)` and `2 * (s₁ + s₃) = (s₀ + s₁) + (s₃ + s₂)`. -/
theorem fc2k_rect_col_pair_bounds {s₀ s₁ s₂ s₃ g : ℕ} {loB hiB : ℝ}
    (hg1 : s₁ = s₀ + g) (hg2 : s₂ = s₃ + g)
    (h01_lo : loB ≤ ((s₀ + s₁ : ℕ) : ℝ)) (h01_hi : ((s₀ + s₁ : ℕ) : ℝ) ≤ hiB)
    (h32_lo : loB ≤ ((s₃ + s₂ : ℕ) : ℝ)) (h32_hi : ((s₃ + s₂ : ℕ) : ℝ) ≤ hiB) :
    loB ≤ ((s₀ + s₂ : ℕ) : ℝ) ∧ ((s₀ + s₂ : ℕ) : ℝ) ≤ hiB ∧
    loB ≤ ((s₁ + s₃ : ℕ) : ℝ) ∧ ((s₁ + s₃ : ℕ) : ℝ) ≤ hiB := by
  have hid1 : 2 * (s₀ + s₂) = (s₀ + s₁) + (s₃ + s₂) := by omega
  have hid2 : 2 * (s₁ + s₃) = (s₀ + s₁) + (s₃ + s₂) := by omega
  have hr1 : 2 * ((s₀ + s₂ : ℕ) : ℝ) = ((s₀ + s₁ : ℕ) : ℝ) + ((s₃ + s₂ : ℕ) : ℝ) := by
    exact_mod_cast hid1
  have hr2 : 2 * ((s₁ + s₃ : ℕ) : ℝ) = ((s₀ + s₁ : ℕ) : ℝ) + ((s₃ + s₂ : ℕ) : ℝ) := by
    exact_mod_cast hid2
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Evaluate the rectangle + `(2 - q)` mean contribution on a single row `r : Fin n`,
proving `(rowCells r ∩ reserved).card ≤ 2` and bounding the combined term in
`[min loB (2 * μ₀), max hiB (2 * μ₀)]`. -/
private theorem fc2k_row_rect_term_bounds {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (a : Cell n ≃ Fin (n * n))
    (rectVal : Fin L × Fin 4 → pool n)
    (hrect_a : ∀ x : Fin L × Fin 4, entry a (packedRectangleCorner hs choice x) = (rectVal x).val)
    {loB hiB μ₀ : ℝ}
    (hpair : ∀ t : Fin L,
      loB ≤ (((rectVal (t, 0)).val + (rectVal (t, 1)).val : ℕ) : ℝ) ∧
      (((rectVal (t, 0)).val + (rectVal (t, 1)).val : ℕ) : ℝ) ≤ hiB ∧
      loB ≤ (((rectVal (t, 3)).val + (rectVal (t, 2)).val : ℕ) : ℝ) ∧
      (((rectVal (t, 3)).val + (rectVal (t, 2)).val : ℕ) : ℝ) ≤ hiB)
    (r : Fin n) :
    let reserved := packedRectangleSupport hs choice
    let q := (rowCells r ∩ reserved).card
    q ≤ 2 ∧
    min loB (2 * μ₀) ≤ (∑ z ∈ rowCells r ∩ reserved, (entry a z : ℝ)) + ((2 - q : ℕ) : ℝ) * μ₀ ∧
    (∑ z ∈ rowCells r ∩ reserved, (entry a z : ℝ)) + ((2 - q : ℕ) : ℝ) * μ₀ ≤ max hiB (2 * μ₀) := by
  let reserved := packedRectangleSupport hs choice
  have h11 := RectanglePacking.firstRow_injective hs
  have h22 := RectanglePacking.secondRow_injective hs
  have h12 := RectanglePacking.firstRow_ne_secondRow hs
  have hfc_ne := RectanglePacking.firstColumn_ne_secondColumn hs choice
  by_cases hex1 : ∃ t : Fin L, RectanglePacking.firstRow hs t = r
  · obtain ⟨t, ht⟩ := hex1
    have hset : rowCells r ∩ reserved =
        {packedRectangleCorner hs choice (t, 0), packedRectangleCorner hs choice (t, 1)} := by
      ext z
      simp only [Finset.mem_inter, mem_rowCells, reserved, packedRectangleSupport,
        Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hzr, ⟨⟨j, s⟩, rfl⟩⟩
        fin_cases s <;> dsimp [packedRectangleCorner] at hzr ⊢
        · subst ht; rw [h11 hzr]; exact Or.inl rfl
        · subst ht; rw [h11 hzr]; exact Or.inr rfl
        · exact False.elim (h12 t j (ht.trans hzr.symm))
        · exact False.elim (h12 t j (ht.trans hzr.symm))
      · rintro (rfl | rfl)
        · exact ⟨ht, ⟨(t, 0), rfl⟩⟩
        · exact ⟨ht, ⟨(t, 1), rfl⟩⟩
    have hne : packedRectangleCorner hs choice (t, 0) ≠ packedRectangleCorner hs choice (t, 1) := by
      intro h; exact hfc_ne t t (congrArg Prod.snd h)
    have hcard : (rowCells r ∩ reserved).card = 2 := by
      rw [hset, Finset.card_pair hne]
    have hsum : (∑ z ∈ rowCells r ∩ reserved, (entry a z : ℝ)) =
        (((rectVal (t, 0)).val + (rectVal (t, 1)).val : ℕ) : ℝ) := by
      rw [hset, Finset.sum_pair hne, hrect_a (t, 0), hrect_a (t, 1), Nat.cast_add]
    refine ⟨le_of_eq hcard, ?_, ?_⟩ <;> rw [hcard, hsum]
    · simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
      exact le_trans (min_le_left _ _) (hpair t).1
    · simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
      exact le_trans (hpair t).2.1 (le_max_left _ _)
  · by_cases hex2 : ∃ t : Fin L, RectanglePacking.secondRow hs t = r
    · obtain ⟨t, ht⟩ := hex2
      have hset : rowCells r ∩ reserved =
          {packedRectangleCorner hs choice (t, 2), packedRectangleCorner hs choice (t, 3)} := by
        ext z
        simp only [Finset.mem_inter, mem_rowCells, reserved, packedRectangleSupport,
          Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hzr, ⟨⟨j, s⟩, rfl⟩⟩
          fin_cases s <;> dsimp [packedRectangleCorner] at hzr ⊢
          · exact False.elim (hex1 ⟨j, hzr⟩)
          · exact False.elim (hex1 ⟨j, hzr⟩)
          · subst ht; rw [h22 hzr]; exact Or.inl rfl
          · subst ht; rw [h22 hzr]; exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact ⟨ht, ⟨(t, 2), rfl⟩⟩
          · exact ⟨ht, ⟨(t, 3), rfl⟩⟩
      have hne : packedRectangleCorner hs choice (t, 2) ≠ packedRectangleCorner hs choice (t, 3) := by
        intro h; exact hfc_ne t t (congrArg Prod.snd h)
      have hcard : (rowCells r ∩ reserved).card = 2 := by
        rw [hset, Finset.card_pair hne]
      have hsum : (∑ z ∈ rowCells r ∩ reserved, (entry a z : ℝ)) =
          (((rectVal (t, 3)).val + (rectVal (t, 2)).val : ℕ) : ℝ) := by
        rw [hset, Finset.sum_pair hne, hrect_a (t, 2), hrect_a (t, 3), Nat.cast_add, add_comm]
      refine ⟨le_of_eq hcard, ?_, ?_⟩ <;> rw [hcard, hsum]
      · simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
        exact le_trans (min_le_left _ _) (hpair t).2.2.1
      · simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
        exact le_trans (hpair t).2.2.2 (le_max_left _ _)
    · have hemp : rowCells r ∩ reserved = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        obtain ⟨hzr, hres⟩ := Finset.mem_inter.mp hz
        rw [mem_rowCells] at hzr
        obtain ⟨⟨j, s⟩, _, heq⟩ := Finset.mem_image.mp hres
        rw [← heq] at hzr
        fin_cases s <;> dsimp [packedRectangleCorner] at hzr
        · exact hex1 ⟨j, hzr⟩
        · exact hex1 ⟨j, hzr⟩
        · exact hex2 ⟨j, hzr⟩
        · exact hex2 ⟨j, hzr⟩
      refine ⟨by rw [hemp]; simp, ?_, ?_⟩
      · rw [hemp]; simp
      · rw [hemp]; simp

/-- Symmetric evaluation of the rectangle + `(2 - q)` mean contribution on a single column `col`. -/
private theorem fc2k_col_rect_term_bounds {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (a : Cell n ≃ Fin (n * n))
    (rectVal : Fin L × Fin 4 → pool n)
    (hrect_a : ∀ x : Fin L × Fin 4, entry a (packedRectangleCorner hs choice x) = (rectVal x).val)
    {loB hiB μ₀ : ℝ}
    (hcol_pair : ∀ t : Fin L,
      loB ≤ (((rectVal (t, 0)).val + (rectVal (t, 2)).val : ℕ) : ℝ) ∧
      (((rectVal (t, 0)).val + (rectVal (t, 2)).val : ℕ) : ℝ) ≤ hiB ∧
      loB ≤ (((rectVal (t, 1)).val + (rectVal (t, 3)).val : ℕ) : ℝ) ∧
      (((rectVal (t, 1)).val + (rectVal (t, 3)).val : ℕ) : ℝ) ≤ hiB)
    (col : Fin n) :
    let reserved := packedRectangleSupport hs choice
    let q := (columnCells col ∩ reserved).card
    q ≤ 2 ∧
    min loB (2 * μ₀) ≤ (∑ z ∈ columnCells col ∩ reserved, (entry a z : ℝ)) + ((2 - q : ℕ) : ℝ) * μ₀ ∧
    (∑ z ∈ columnCells col ∩ reserved, (entry a z : ℝ)) + ((2 - q : ℕ) : ℝ) * μ₀ ≤ max hiB (2 * μ₀) := by
  let reserved := packedRectangleSupport hs choice
  have h11 := RectanglePacking.firstColumn_injective hs choice
  have h22 := RectanglePacking.secondColumn_injective hs choice
  have h12 := RectanglePacking.firstColumn_ne_secondColumn hs choice
  have hfr_ne := RectanglePacking.firstRow_ne_secondRow hs
  by_cases hex1 : ∃ t : Fin L, RectanglePacking.firstColumn hs choice t = col
  · obtain ⟨t, ht⟩ := hex1
    have hset : columnCells col ∩ reserved =
        {packedRectangleCorner hs choice (t, 0), packedRectangleCorner hs choice (t, 2)} := by
      ext z
      simp only [Finset.mem_inter, mem_columnCells, reserved, packedRectangleSupport,
        Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hzc, ⟨⟨j, s⟩, rfl⟩⟩
        fin_cases s <;> dsimp [packedRectangleCorner] at hzc ⊢
        · subst ht; rw [h11 hzc]; exact Or.inl rfl
        · exact False.elim (h12 t j (ht.trans hzc.symm))
        · subst ht; rw [h11 hzc]; exact Or.inr rfl
        · exact False.elim (h12 t j (ht.trans hzc.symm))
      · rintro (rfl | rfl)
        · exact ⟨ht, ⟨(t, 0), rfl⟩⟩
        · exact ⟨ht, ⟨(t, 2), rfl⟩⟩
    have hne : packedRectangleCorner hs choice (t, 0) ≠ packedRectangleCorner hs choice (t, 2) := by
      intro h; exact hfr_ne t t (congrArg Prod.fst h)
    have hcard : (columnCells col ∩ reserved).card = 2 := by
      rw [hset, Finset.card_pair hne]
    have hsum : (∑ z ∈ columnCells col ∩ reserved, (entry a z : ℝ)) =
        (((rectVal (t, 0)).val + (rectVal (t, 2)).val : ℕ) : ℝ) := by
      rw [hset, Finset.sum_pair hne, hrect_a (t, 0), hrect_a (t, 2), Nat.cast_add]
    refine ⟨le_of_eq hcard, ?_, ?_⟩ <;> rw [hcard, hsum]
    · simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
      exact le_trans (min_le_left _ _) (hcol_pair t).1
    · simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
      exact le_trans (hcol_pair t).2.1 (le_max_left _ _)
  · by_cases hex2 : ∃ t : Fin L, RectanglePacking.secondColumn hs choice t = col
    · obtain ⟨t, ht⟩ := hex2
      have hset : columnCells col ∩ reserved =
          {packedRectangleCorner hs choice (t, 1), packedRectangleCorner hs choice (t, 3)} := by
        ext z
        simp only [Finset.mem_inter, mem_columnCells, reserved, packedRectangleSupport,
          Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hzc, ⟨⟨j, s⟩, rfl⟩⟩
          fin_cases s <;> dsimp [packedRectangleCorner] at hzc ⊢
          · exact False.elim (hex1 ⟨j, hzc⟩)
          · subst ht; rw [h22 hzc]; exact Or.inl rfl
          · exact False.elim (hex1 ⟨j, hzc⟩)
          · subst ht; rw [h22 hzc]; exact Or.inr rfl
        · rintro (rfl | rfl)
          · exact ⟨ht, ⟨(t, 1), rfl⟩⟩
          · exact ⟨ht, ⟨(t, 3), rfl⟩⟩
      have hne : packedRectangleCorner hs choice (t, 1) ≠ packedRectangleCorner hs choice (t, 3) := by
        intro h; exact hfr_ne t t (congrArg Prod.fst h)
      have hcard : (columnCells col ∩ reserved).card = 2 := by
        rw [hset, Finset.card_pair hne]
      have hsum : (∑ z ∈ columnCells col ∩ reserved, (entry a z : ℝ)) =
          (((rectVal (t, 1)).val + (rectVal (t, 3)).val : ℕ) : ℝ) := by
        rw [hset, Finset.sum_pair hne, hrect_a (t, 1), hrect_a (t, 3), Nat.cast_add]
      refine ⟨le_of_eq hcard, ?_, ?_⟩ <;> rw [hcard, hsum]
      · simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
        exact le_trans (min_le_left _ _) (hcol_pair t).2.2.1
      · simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
        exact le_trans (hcol_pair t).2.2.2 (le_max_left _ _)
    · have hemp : columnCells col ∩ reserved = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        obtain ⟨hzc, hres⟩ := Finset.mem_inter.mp hz
        rw [mem_columnCells] at hzc
        obtain ⟨⟨j, s⟩, _, heq⟩ := Finset.mem_image.mp hres
        rw [← heq] at hzc
        fin_cases s <;> dsimp [packedRectangleCorner] at hzc
        · exact hex1 ⟨j, hzc⟩
        · exact hex2 ⟨j, hzc⟩
        · exact hex1 ⟨j, hzc⟩
        · exact hex2 ⟨j, hzc⟩
      refine ⟨by rw [hemp]; simp, ?_, ?_⟩
      · rw [hemp]; simp
      · rw [hemp]; simp

/-- Exact ordinary row-sum + `R_div` midpoint identity: on row `r`, the sum of installed
`layersSupport rows` and `transposeCells (layersSupport cols)` entries plus `(1/2)` of the
edge-radius divergence equals the exact 6-block midpoint sum across all `S` stages. -/
private theorem fc2k_row_ord_midpoint_eq {S n : ℕ} {res₁ res₂ : Finset (Cell n)}
    (p : Fin 3 → Equiv.Perm (Fin n))
    (rows cols : List (LayerPacking.Layer n))
    (hrS : rows.length = S * 3) (hcS : cols.length = S * 3)
    (hrmap : rows.map Prod.fst = bridgeRepeatedPermutations S p)
    (hr : LayerPacking.PackedLayers res₁ rows)
    (hc : LayerPacking.PackedLayers res₂ cols)
    (a : Cell n ≃ Fin (n * n))
    (rowVal colVal : Fin (S * 3) × (Fin n × Bool) → pool n)
    (ordGap : Fin (S * 3) → Fin n → ℕ)
    (hrow_gap : ∀ i e, (rowVal (i, (e, true))).val = (rowVal (i, (e, false))).val + ordGap i e)
    (hrow_a : ∀ x, entry a (LayerPacking.sequenceCell rows x) = (rowVal (Fin.cast hrS x.1, x.2)).val)
    (hcol_a : ∀ x, entry a (LayerPacking.sequenceCell cols x).swap = (colVal (Fin.cast hcS x.1, x.2)).val)
    (edgeRadius : Fin 3 × Fin n → ℕ)
    (hedge_sum : ∀ e : Fin 3 × Fin n, edgeRadius e =
      ∑ k ∈ (Finset.univ : Finset (Fin S)).image
        (fun s => (bridgeStageLayerIndex (r := 3) (J := S) rfl s e.1, e.2)), ordGap k.1 k.2)
    (r : Fin n) :
    (∑ z ∈ rowCells r ∩ LayerPacking.layersSupport rows, (entry a z : ℝ)) +
    (∑ z ∈ rowCells r ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols), (entry a z : ℝ)) +
    (1 / 2 : ℝ) * (∑ e : Fin 3 × Fin n,
      (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (edgeRadius e : ℤ)) e r : ℝ)) =
    ∑ s : Fin S, ∑ l : Fin 3,
      (let idx := bridgeStageLayerIndex (r := 3) (J := S) rfl s l
       let gc := (cols.get (bridgeStageLayerIndex hcS s l)).2
       ((((rowVal (idx, (r, false))).val + (rowVal (idx, (r, true))).val : ℕ) : ℝ) +
        (((rowVal (idx, ((p l).symm r, false))).val + (rowVal (idx, ((p l).symm r, true))).val : ℕ) : ℝ)) / 2 +
       ((((colVal (idx, (gc.symm r, false))).val + (colVal (idx, (gc.symm r, true))).val : ℕ) : ℝ) +
        (((colVal (idx, (gc.symm r, false))).val + (colVal (idx, (gc.symm r, true))).val : ℕ) : ℝ)) / 2) := by
  have hfilter_inter : ∀ (T : Finset (Cell n)),
      (∑ z ∈ rowCells r ∩ T, (entry a z : ℝ)) = ∑ z ∈ T, (if z.1 = r then (entry a z : ℝ) else 0) := by
    intro T
    have heq : rowCells r ∩ T = T.filter (fun z => z.1 = r) := by
      ext z; simp [and_comm]
    rw [heq, Finset.sum_filter]
  -- 1. Evaluate row-network sum
  have hrow_sum : (∑ z ∈ rowCells r ∩ LayerPacking.layersSupport rows, (entry a z : ℝ)) =
      ∑ s : Fin S, ∑ l : Fin 3,
        (let idx := bridgeStageLayerIndex (r := 3) (J := S) rfl s l
         (((rowVal (idx, (r, false))).val : ℝ) + ((rowVal (idx, ((p l).symm r, true))).val : ℝ))) := by
    rw [hfilter_inter, layersSupport_eq_image_sequenceCell rows,
      Finset.sum_image (fun x _ y _ h => hr.sequenceCell_injective h),
      Fintype.sum_prod_type]
    let eR : Fin S × Fin 3 ≃ Fin rows.length := finProdFinEquiv.trans (finCongr hrS.symm)
    rw [← Equiv.sum_comp eR, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro l _
    have heR_eq : eR (s, l) = bridgeStageLayerIndex hrS s l := rfl
    rw [heR_eq, Fintype.sum_prod_type]
    have hcast_eq : Fin.cast hrS (bridgeStageLayerIndex hrS s l) =
        bridgeStageLayerIndex (r := 3) (J := S) rfl s l := by
      ext; simp [bridgeStageLayerIndex]
    have hπ_eq : ∀ e : Fin n, (rows.get (bridgeStageLayerIndex hrS s l)).1 e = p l e :=
      fun e => bridgeStageLayer_endpoints rows hrS p hrmap s l e
    have hinner : ∀ e : Fin n,
        (∑ b : Bool, (if (LayerPacking.sequenceCell rows (bridgeStageLayerIndex hrS s l, (e, b))).1 = r then
            (entry a (LayerPacking.sequenceCell rows (bridgeStageLayerIndex hrS s l, (e, b))) : ℝ) else 0)) =
        (if e = r then ((rowVal (bridgeStageLayerIndex rfl s l, (e, false))).val : ℝ) else 0) +
        (if p l e = r then ((rowVal (bridgeStageLayerIndex rfl s l, (e, true))).val : ℝ) else 0) := by
      intro e
      rw [Fintype.sum_bool, hrow_a, hrow_a, hcast_eq]
      have h1 : (LayerPacking.sequenceCell rows (bridgeStageLayerIndex hrS s l, (e, true))).1 = p l e := hπ_eq e
      have h2 : (LayerPacking.sequenceCell rows (bridgeStageLayerIndex hrS s l, (e, false))).1 = e := rfl
      rw [h1, h2, add_comm]
    simp only [hinner, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    congr 1
    rw [← Equiv.sum_comp (p l).symm]
    simp only [Equiv.apply_symm_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  -- 2. Evaluate transposed col-network sum
  have hcol_sum : (∑ z ∈ rowCells r ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols), (entry a z : ℝ)) =
      ∑ s : Fin S, ∑ l : Fin 3,
        (let idx := bridgeStageLayerIndex (r := 3) (J := S) rfl s l
         let gc := (cols.get (bridgeStageLayerIndex hcS s l)).2
         (((colVal (idx, (gc.symm r, false))).val : ℝ) + ((colVal (idx, (gc.symm r, true))).val : ℝ))) := by
    have hc_inj : Function.Injective (fun x => (LayerPacking.sequenceCell cols x).swap) :=
      Prod.swap_injective.comp hc.sequenceCell_injective
    rw [hfilter_inter, transposeCells_layersSupport_eq_image cols,
      Finset.sum_image (fun x _ y _ h => hc_inj h), Fintype.sum_prod_type]
    let eC : Fin S × Fin 3 ≃ Fin cols.length := finProdFinEquiv.trans (finCongr hcS.symm)
    rw [← Equiv.sum_comp eC, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro l _
    have heC_eq : eC (s, l) = bridgeStageLayerIndex hcS s l := rfl
    rw [heC_eq, Fintype.sum_prod_type]
    have hcast_eq : Fin.cast hcS (bridgeStageLayerIndex hcS s l) =
        bridgeStageLayerIndex (r := 3) (J := S) rfl s l := by
      ext; simp [bridgeStageLayerIndex]
    set gc := (cols.get (bridgeStageLayerIndex hcS s l)).2
    have hinner : ∀ e : Fin n,
        (∑ b : Bool, (if ((LayerPacking.sequenceCell cols (bridgeStageLayerIndex hcS s l, (e, b))).swap).1 = r then
            (entry a (LayerPacking.sequenceCell cols (bridgeStageLayerIndex hcS s l, (e, b))).swap : ℝ) else 0)) =
        (if gc e = r then
          ((colVal (bridgeStageLayerIndex rfl s l, (e, false))).val : ℝ) +
          ((colVal (bridgeStageLayerIndex rfl s l, (e, true))).val : ℝ) else 0) := by
      intro e
      rw [Fintype.sum_bool, hcol_a, hcol_a, hcast_eq]
      have h1 : ((LayerPacking.sequenceCell cols (bridgeStageLayerIndex hcS s l, (e, true))).swap).1 = gc e := rfl
      have h2 : ((LayerPacking.sequenceCell cols (bridgeStageLayerIndex hcS s l, (e, false))).swap).1 = gc e := rfl
      rw [h1, h2]
      split_ifs <;> ring
    simp only [hinner]
    rw [← Equiv.sum_comp gc.symm]
    simp only [Equiv.apply_symm_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  -- 3. Evaluate R_div
  have hrad_eq : ∀ (l : Fin 3) (e : Fin n),
      (edgeRadius (l, e) : ℝ) = ∑ s : Fin S, (ordGap (bridgeStageLayerIndex rfl s l) e : ℝ) := by
    intro l e
    rw [hedge_sum (l, e), Finset.sum_image]
    · push_cast; rfl
    · intro s₁ _ s₂ _ h
      exact bridgeStageLayerIndex_injective rfl l (congrArg Prod.fst h)
  have hdiv_sum : (∑ e : Fin 3 × Fin n,
      (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (edgeRadius e : ℤ)) e r : ℝ)) =
      ∑ s : Fin S, ∑ l : Fin 3,
        ((ordGap (bridgeStageLayerIndex rfl s l) r : ℝ) -
         (ordGap (bridgeStageLayerIndex rfl s l) ((p l).symm r) : ℝ)) := by
    rw [Fintype.sum_prod_type]
    have hper_l : ∀ l : Fin 3,
        (∑ e : Fin n, (edgeTransfer Prod.snd (fun x : Fin 3 × Fin n => p x.1 x.2)
          (fun x => (edgeRadius x : ℤ)) (l, e) r : ℝ)) =
        (edgeRadius (l, r) : ℝ) - (edgeRadius (l, (p l).symm r) : ℝ) := by
      intro l
      have hcast_et : ∀ e : Fin n,
          (edgeTransfer Prod.snd (fun x : Fin 3 × Fin n => p x.1 x.2)
            (fun x => (edgeRadius x : ℤ)) (l, e) r : ℝ) =
          (if e = r then (edgeRadius (l, e) : ℝ) else 0) -
          (if p l e = r then (edgeRadius (l, e) : ℝ) else 0) := by
        intro e; unfold edgeTransfer; dsimp only; split_ifs <;> push_cast <;> ring
      simp only [hcast_et, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      congr 1
      rw [← Equiv.sum_comp (p l).symm]
      simp only [Equiv.apply_symm_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    simp only [hper_l, hrad_eq, ← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
  -- 4. Combine stage by stage
  rw [hrow_sum, hcol_sum, hdiv_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro l _
  set idx := bridgeStageLayerIndex (r := 3) (J := S) rfl s l
  have hg1 : ((rowVal (idx, (r, true))).val : ℝ) =
      ((rowVal (idx, (r, false))).val : ℝ) + (ordGap idx r : ℝ) := by
    exact_mod_cast hrow_gap idx r
  have hg2 : ((rowVal (idx, ((p l).symm r, true))).val : ℝ) =
      ((rowVal (idx, ((p l).symm r, false))).val : ℝ) + (ordGap idx ((p l).symm r) : ℝ) := by
    exact_mod_cast hrow_gap idx ((p l).symm r)
  dsimp only
  push_cast
  linarith

/-- Symmetric column-sum + `C_div` midpoint identity on column `col : Fin n`. -/
private theorem fc2k_col_ord_midpoint_eq {S n : ℕ} {res₁ res₂ : Finset (Cell n)}
    (p : Fin 3 → Equiv.Perm (Fin n))
    (rows cols : List (LayerPacking.Layer n))
    (hrS : rows.length = S * 3) (hcS : cols.length = S * 3)
    (hcmap : cols.map Prod.fst = bridgeRepeatedPermutations S p)
    (hr : LayerPacking.PackedLayers res₁ rows)
    (hc : LayerPacking.PackedLayers res₂ cols)
    (a : Cell n ≃ Fin (n * n))
    (rowVal colVal : Fin (S * 3) × (Fin n × Bool) → pool n)
    (ordGap : Fin (S * 3) → Fin n → ℕ)
    (hcol_gap : ∀ i e, (colVal (i, (e, true))).val = (colVal (i, (e, false))).val + ordGap i e)
    (hrow_a : ∀ x, entry a (LayerPacking.sequenceCell rows x) = (rowVal (Fin.cast hrS x.1, x.2)).val)
    (hcol_a : ∀ x, entry a (LayerPacking.sequenceCell cols x).swap = (colVal (Fin.cast hcS x.1, x.2)).val)
    (edgeRadius : Fin 3 × Fin n → ℕ)
    (hedge_sum : ∀ e : Fin 3 × Fin n, edgeRadius e =
      ∑ k ∈ (Finset.univ : Finset (Fin S)).image
        (fun s => (bridgeStageLayerIndex (r := 3) (J := S) rfl s e.1, e.2)), ordGap k.1 k.2)
    (col : Fin n) :
    (∑ z ∈ columnCells col ∩ LayerPacking.layersSupport rows, (entry a z : ℝ)) +
    (∑ z ∈ columnCells col ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols), (entry a z : ℝ)) +
    (1 / 2 : ℝ) * (∑ e : Fin 3 × Fin n,
      (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (edgeRadius e : ℤ)) e col : ℝ)) =
    ∑ s : Fin S, ∑ l : Fin 3,
      (let idx := bridgeStageLayerIndex (r := 3) (J := S) rfl s l
       let gr := (rows.get (bridgeStageLayerIndex hrS s l)).2
       ((((rowVal (idx, (gr.symm col, false))).val + (rowVal (idx, (gr.symm col, true))).val : ℕ) : ℝ) +
        (((rowVal (idx, (gr.symm col, false))).val + (rowVal (idx, (gr.symm col, true))).val : ℕ) : ℝ)) / 2 +
       ((((colVal (idx, (col, false))).val + (colVal (idx, (col, true))).val : ℕ) : ℝ) +
        (((colVal (idx, ((p l).symm col, false))).val + (colVal (idx, ((p l).symm col, true))).val : ℕ) : ℝ)) / 2) := by
  have hfilter_inter : ∀ (T : Finset (Cell n)),
      (∑ z ∈ columnCells col ∩ T, (entry a z : ℝ)) = ∑ z ∈ T, (if z.2 = col then (entry a z : ℝ) else 0) := by
    intro T
    have heq : columnCells col ∩ T = T.filter (fun z => z.2 = col) := by
      ext z; simp [and_comm]
    rw [heq, Finset.sum_filter]
  -- 1. Evaluate row-network sum on column `col`
  have hrow_sum : (∑ z ∈ columnCells col ∩ LayerPacking.layersSupport rows, (entry a z : ℝ)) =
      ∑ s : Fin S, ∑ l : Fin 3,
        (let idx := bridgeStageLayerIndex (r := 3) (J := S) rfl s l
         let gr := (rows.get (bridgeStageLayerIndex hrS s l)).2
         (((rowVal (idx, (gr.symm col, false))).val : ℝ) + ((rowVal (idx, (gr.symm col, true))).val : ℝ))) := by
    rw [hfilter_inter, layersSupport_eq_image_sequenceCell rows,
      Finset.sum_image (fun x _ y _ h => hr.sequenceCell_injective h),
      Fintype.sum_prod_type]
    let eR : Fin S × Fin 3 ≃ Fin rows.length := finProdFinEquiv.trans (finCongr hrS.symm)
    rw [← Equiv.sum_comp eR, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro l _
    have heR_eq : eR (s, l) = bridgeStageLayerIndex hrS s l := rfl
    rw [heR_eq, Fintype.sum_prod_type]
    have hcast_eq : Fin.cast hrS (bridgeStageLayerIndex hrS s l) =
        bridgeStageLayerIndex (r := 3) (J := S) rfl s l := by
      ext; simp [bridgeStageLayerIndex]
    set gr := (rows.get (bridgeStageLayerIndex hrS s l)).2
    have hinner : ∀ e : Fin n,
        (∑ b : Bool, (if (LayerPacking.sequenceCell rows (bridgeStageLayerIndex hrS s l, (e, b))).2 = col then
            (entry a (LayerPacking.sequenceCell rows (bridgeStageLayerIndex hrS s l, (e, b))) : ℝ) else 0)) =
        (if gr e = col then
          ((rowVal (bridgeStageLayerIndex rfl s l, (e, false))).val : ℝ) +
          ((rowVal (bridgeStageLayerIndex rfl s l, (e, true))).val : ℝ) else 0) := by
      intro e
      rw [Fintype.sum_bool, hrow_a, hrow_a, hcast_eq]
      have h1 : (LayerPacking.sequenceCell rows (bridgeStageLayerIndex hrS s l, (e, true))).2 = gr e := rfl
      have h2 : (LayerPacking.sequenceCell rows (bridgeStageLayerIndex hrS s l, (e, false))).2 = gr e := rfl
      rw [h1, h2]
      split_ifs <;> ring
    simp only [hinner]
    rw [← Equiv.sum_comp gr.symm]
    simp only [Equiv.apply_symm_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  -- 2. Evaluate transposed col-network sum on column `col`
  have hcol_sum : (∑ z ∈ columnCells col ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols), (entry a z : ℝ)) =
      ∑ s : Fin S, ∑ l : Fin 3,
        (let idx := bridgeStageLayerIndex (r := 3) (J := S) rfl s l
         (((colVal (idx, (col, false))).val : ℝ) + ((colVal (idx, ((p l).symm col, true))).val : ℝ))) := by
    have hc_inj : Function.Injective (fun x => (LayerPacking.sequenceCell cols x).swap) :=
      Prod.swap_injective.comp hc.sequenceCell_injective
    rw [hfilter_inter, transposeCells_layersSupport_eq_image cols,
      Finset.sum_image (fun x _ y _ h => hc_inj h), Fintype.sum_prod_type]
    let eC : Fin S × Fin 3 ≃ Fin cols.length := finProdFinEquiv.trans (finCongr hcS.symm)
    rw [← Equiv.sum_comp eC, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro l _
    have heC_eq : eC (s, l) = bridgeStageLayerIndex hcS s l := rfl
    rw [heC_eq, Fintype.sum_prod_type]
    have hcast_eq : Fin.cast hcS (bridgeStageLayerIndex hcS s l) =
        bridgeStageLayerIndex (r := 3) (J := S) rfl s l := by
      ext; simp [bridgeStageLayerIndex]
    have hπ_eq : ∀ e : Fin n, (cols.get (bridgeStageLayerIndex hcS s l)).1 e = p l e :=
      fun e => bridgeStageLayer_endpoints cols hcS p hcmap s l e
    have hinner : ∀ e : Fin n,
        (∑ b : Bool, (if ((LayerPacking.sequenceCell cols (bridgeStageLayerIndex hcS s l, (e, b))).swap).2 = col then
            (entry a (LayerPacking.sequenceCell cols (bridgeStageLayerIndex hcS s l, (e, b))).swap : ℝ) else 0)) =
        (if e = col then ((colVal (bridgeStageLayerIndex rfl s l, (e, false))).val : ℝ) else 0) +
        (if p l e = col then ((colVal (bridgeStageLayerIndex rfl s l, (e, true))).val : ℝ) else 0) := by
      intro e
      rw [Fintype.sum_bool, hcol_a, hcol_a, hcast_eq]
      have h1 : ((LayerPacking.sequenceCell cols (bridgeStageLayerIndex hcS s l, (e, true))).swap).2 = p l e := hπ_eq e
      have h2 : ((LayerPacking.sequenceCell cols (bridgeStageLayerIndex hcS s l, (e, false))).swap).2 = e := rfl
      rw [h1, h2, add_comm]
    simp only [hinner, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    congr 1
    rw [← Equiv.sum_comp (p l).symm]
    simp only [Equiv.apply_symm_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  -- 3. Evaluate C_div
  have hrad_eq : ∀ (l : Fin 3) (e : Fin n),
      (edgeRadius (l, e) : ℝ) = ∑ s : Fin S, (ordGap (bridgeStageLayerIndex rfl s l) e : ℝ) := by
    intro l e
    rw [hedge_sum (l, e), Finset.sum_image]
    · push_cast; rfl
    · intro s₁ _ s₂ _ h
      exact bridgeStageLayerIndex_injective rfl l (congrArg Prod.fst h)
  have hdiv_sum : (∑ e : Fin 3 × Fin n,
      (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (edgeRadius e : ℤ)) e col : ℝ)) =
      ∑ s : Fin S, ∑ l : Fin 3,
        ((ordGap (bridgeStageLayerIndex rfl s l) col : ℝ) -
         (ordGap (bridgeStageLayerIndex rfl s l) ((p l).symm col) : ℝ)) := by
    rw [Fintype.sum_prod_type]
    have hper_l : ∀ l : Fin 3,
        (∑ e : Fin n, (edgeTransfer Prod.snd (fun x : Fin 3 × Fin n => p x.1 x.2)
          (fun x => (edgeRadius x : ℤ)) (l, e) col : ℝ)) =
        (edgeRadius (l, col) : ℝ) - (edgeRadius (l, (p l).symm col) : ℝ) := by
      intro l
      have hcast_et : ∀ e : Fin n,
          (edgeTransfer Prod.snd (fun x : Fin 3 × Fin n => p x.1 x.2)
            (fun x => (edgeRadius x : ℤ)) (l, e) col : ℝ) =
          (if e = col then (edgeRadius (l, e) : ℝ) else 0) -
          (if p l e = col then (edgeRadius (l, e) : ℝ) else 0) := by
        intro e; unfold edgeTransfer; dsimp only; split_ifs <;> push_cast <;> ring
      simp only [hcast_et, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      congr 1
      rw [← Equiv.sum_comp (p l).symm]
      simp only [Equiv.apply_symm_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    simp only [hper_l, hrad_eq, ← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
  -- 4. Combine stage by stage
  rw [hrow_sum, hcol_sum, hdiv_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro l _
  set idx := bridgeStageLayerIndex (r := 3) (J := S) rfl s l
  have hg1 : ((colVal (idx, (col, true))).val : ℝ) =
      ((colVal (idx, (col, false))).val : ℝ) + (ordGap idx col : ℝ) := by
    exact_mod_cast hcol_gap idx col
  have hg2 : ((colVal (idx, ((p l).symm col, true))).val : ℝ) =
      ((colVal (idx, ((p l).symm col, false))).val : ℝ) + (ordGap idx ((p l).symm col) : ℝ) := by
    exact_mod_cast hcol_gap idx ((p l).symm col)
  dsimp only
  push_cast
  linarith

/-- Bundled completed physical square and centered routing networks for FC2K. -/
structure FC2KCompletedWitness
    (n P qCert corrLo maxHi J_max W_ord W_diag N_bins : ℕ) (δ ε μ_lo μ_hi : ℝ)
    (prof : GeneralPrefixProfile P qCert corrLo maxHi)
    (roles : FC2KSelectedRoles n P qCert corrLo maxHi J_max W_ord W_diag N_bins δ prof) where
  L : ℕ
  hL_def : L = 24 * P + 24 * roles.J + 2 * W_diag
  hs : 2 * L + 1 ≤ n
  hL : 3 ≤ L
  choice : Fin L → Bool
  hchoice : choice = fc2kDiagChoice L
  p : Fin 3 → Equiv.Perm (Fin n)
  hderange : ∀ i v, p i v ≠ v
  hexp : ∀ S : Finset (Fin n), 199 * min S.card (n - S.card) ≤
    200 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card
  rows : List (LayerPacking.Layer n)
  cols : List (LayerPacking.Layer n)
  hrS : rows.length = (P + roles.J + W_ord) * 3
  hcS : cols.length = (P + roles.J + W_ord) * 3
  hr : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows
  hc : LayerPacking.PackedLayers
    (LayerPacking.transposeCells (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols
  a : Cell n ≃ Fin (n * n)
  c : Cell n ≃ Fin (n * n)
  hrect_c : ∀ x : Fin L × Fin 4, entry c (packedRectangleCorner hs choice x) =
    (roles.rectVal (Fin.cast hL_def x.1, x.2)).val
  rowGap : Fin rows.length → Fin n → ℕ
  colGap : Fin cols.length → Fin n → ℕ
  hrowGap_c : ∀ i e, entry c ((rows.get i).1 e, (rows.get i).2 e) =
    entry c (e, (rows.get i).2 e) + rowGap i e
  hcolGap_c : ∀ i e, entry c ((cols.get i).2 e, (cols.get i).1 e) =
    entry c ((cols.get i).2 e, e) + colGap i e
  BR : CenteredNetwork (Fin 3 × Fin n) (Fin rows.length × Fin n)
    (hr.rowPairs c rowGap hrowGap_c)
  BC : CenteredNetwork (Fin 3 × Fin n) (Fin cols.length × Fin n)
    (hc.columnPairs c colGap hcolGap_c)
  hends : ∀ e, BR.source e = e.2 ∧ BC.source e = e.2 ∧
    BR.target e = p e.1 e.2 ∧ BC.target e = p e.1 e.2
  hR_rad : ∀ e, BR.radius e = roles.edgeRadius e
  hC_rad : ∀ e, BC.radius e = roles.edgeRadius e
  μ₀ : ℝ
  hμ₀_bounds : μ_lo ≤ μ₀ ∧ μ₀ ≤ μ_hi
  hmain_diff_c : |(mainSum c : ℝ) + (roles.Rm : ℝ) / 2 -
    ((antiSum c : ℝ) + (roles.Ra : ℝ) / 2)| ≤
    ((prof.totalSpanWords * 49152 : ℕ) : ℝ) +
    (9 / 25 : ℝ) * (roles.J : ℝ) * (poolMaximum n : ℝ) +
    (W_diag : ℝ) * δ * (poolMaximum n : ℝ) +
    (401 / 100 : ℝ) * ε * (poolMaximum n : ℝ)
  hmain_lo_c :
    ((n - (12 * P + 12 * J_max + W_diag) : ℕ) : ℝ) * μ_lo -
      2 * ε * (poolMaximum n : ℝ) ≤ (mainSum c : ℝ)
  M_row_ideal : Fin n → ℝ
  M_col_ideal : Fin n → ℝ
  hrow_ideal_sum : ∑ r : Fin n, M_row_ideal r = (Lucas.poolTotal n : ℝ)
  hcol_ideal_sum : ∑ col : Fin n, M_col_ideal col = (Lucas.poolTotal n : ℝ)
  hrow_c_approx : ∀ r : Fin n,
    |((rowSum c r : ℝ) + (1 / 2 : ℝ) * ∑ e : Fin 3 × Fin n,
        (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (BR.radius e : ℤ)) e r : ℝ)) -
      M_row_ideal r| < (1 + 10 * ε) * (poolMaximum n : ℝ)
  hcol_c_approx : ∀ col : Fin n,
    |((columnSum c col : ℝ) + (1 / 2 : ℝ) * ∑ e : Fin 3 × Fin n,
        (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (BC.radius e : ℤ)) e col : ℝ)) -
      M_col_ideal col| < (1 + 10 * ε) * (poolMaximum n : ℝ)
  hrow_ideal_width : ∀ r₁ r₂ : Fin n,
    let loB := min (min (2 * (corrLo : ℝ)) (min ((197 / 200 : ℝ) * (poolMaximum n : ℝ))
      (2 * fc2kPoolMean n - δ * (poolMaximum n : ℝ)))) (2 * μ₀)
    let hiB := max (max (2 * (maxHi : ℝ)) (max ((203 / 200 : ℝ) * (poolMaximum n : ℝ))
      (2 * fc2kPoolMean n + δ * (poolMaximum n : ℝ)))) (2 * μ₀)
    |M_row_ideal r₁ - M_row_ideal r₂| ≤
      (hiB - loB) + ((2 * prof.totalSpanWords * 49152 : ℕ) : ℝ) +
      (9 / 50 : ℝ) * (roles.J : ℝ) * (poolMaximum n : ℝ) +
      12 * (W_ord : ℝ) * δ * (poolMaximum n : ℝ)
  hcol_ideal_width : ∀ c₁ c₂ : Fin n,
    let loB := min (min (2 * (corrLo : ℝ)) (min ((197 / 200 : ℝ) * (poolMaximum n : ℝ))
      (2 * fc2kPoolMean n - δ * (poolMaximum n : ℝ)))) (2 * μ₀)
    let hiB := max (max (2 * (maxHi : ℝ)) (max ((203 / 200 : ℝ) * (poolMaximum n : ℝ))
      (2 * fc2kPoolMean n + δ * (poolMaximum n : ℝ)))) (2 * μ₀)
    |M_col_ideal c₁ - M_col_ideal c₂| ≤
      (hiB - loB) + ((2 * prof.totalSpanWords * 49152 : ℕ) : ℝ) +
      (9 / 50 : ℝ) * (roles.J : ℝ) * (poolMaximum n : ℝ) +
      12 * (W_ord : ℝ) * δ * (poolMaximum n : ℝ)

/-- Jointly install rectangles + two permutation-expander networks and execute sharp central-band
completion to construct a full `FC2KCompletedWitness`. -/
theorem fc2k_joint_install_and_complete
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    {n P qCert corrLo maxHi J_max W_ord W_diag N_bins P_half P_full : ℕ}
    {δ ε μ_lo μ_hi : ℝ}
    {prof : GeneralPrefixProfile P qCert corrLo maxHi}
    (roles : FC2KSelectedRoles n P qCert corrLo maxHi J_max W_ord W_diag N_bins δ prof)
    (hn : 2001 ≤ n) (hnmax : n ≤ 19483) (hodd : Odd n) (hP : 1 ≤ P) (hε : 0 < ε)
    (hs_max : 2 * (24 * P + 24 * J_max + 2 * W_diag) + 1 ≤ n)
    (hload_max : 4 * (12 * (P + J_max + W_ord) + 4) + 8 < n)
    (hres_max : 4 * (12 * P * (n + 8) + 12 * J_max * (n + 8) + 8 * W_diag + 12 * W_ord * n) ≤ n * n)
    (hμ_bounds : ∀ J ≤ J_max,
      let N_rem : ℝ := ((n * n - (12 * P * (n + 8) + 12 * J * (n + 8) + 8 * W_diag + 12 * W_ord * n) : ℕ) : ℝ)
      let S_lo : ℝ := 12 * (P : ℝ) * ((n : ℝ) + 8) * (corrLo : ℝ) +
        6 * (J : ℝ) * ((n : ℝ) + 8) * ((197 / 200 : ℝ) * (poolMaximum n : ℝ)) +
        (2 * (W_diag : ℝ) + (W_ord : ℝ) * (3 * (n : ℝ))) *
          (4 * fc2kPoolMean n - 2 * δ * (poolMaximum n : ℝ))
      let S_hi : ℝ := 12 * (P : ℝ) * ((n : ℝ) + 8) * (maxHi : ℝ) +
        6 * (J : ℝ) * ((n : ℝ) + 8) * ((203 / 200 : ℝ) * (poolMaximum n : ℝ)) +
        (2 * (W_diag : ℝ) + (W_ord : ℝ) * (3 * (n : ℝ))) *
          (4 * fc2kPoolMean n + 2 * δ * (poolMaximum n : ℝ))
      μ_lo * N_rem ≤ (Lucas.poolTotal n : ℝ) - S_hi ∧
      (Lucas.poolTotal n : ℝ) - S_lo ≤ μ_hi * N_rem)
    (hwide_sep_cent :
      let X : ℝ := poolMaximum n
      let δ_sh : ℝ := 6 * (ε * X) / ((n * n - 1 : ℕ) : ℝ)
      ((1 / 500 : ℝ) + (N_bins : ℝ) * δ) * X ≤ μ_lo - ε * X - δ_sh ∧
      μ_hi + ε * X + δ_sh ≤ 2 * fc2kPoolMean n - ((1 / 500 : ℝ) + (N_bins : ℝ) * δ) * X)
    (hcent_in_pool :
      let X : ℝ := poolMaximum n
      let δ_sh : ℝ := 6 * (ε * X) / ((n * n - 1 : ℕ) : ℝ)
      1 ≤ μ_lo - ε * X - δ_sh ∧ μ_hi + ε * X + δ_sh ≤ X)
    (hP_half : ∀ lo hi : ℝ,
      μ_lo - ε * (poolMaximum n : ℝ) ≤ lo →
      hi ≤ μ_hi + ε * (poolMaximum n : ℝ) →
      lo ≤ hi →
      hi - lo ≤ (ε / 2) * (poolMaximum n : ℝ) →
      (roles.V_pref ∩ apInterval lo hi 2 1).card ≤ P_half)
    (hP_full : ∀ lo hi : ℝ,
      let X : ℝ := poolMaximum n
      let δ_sh : ℝ := 6 * (ε * X) / ((n * n - 1 : ℕ) : ℝ)
      μ_lo - ε * X - δ_sh ≤ lo →
      hi ≤ μ_hi + ε * X + δ_sh →
      lo ≤ hi →
      hi - lo ≤ 2 * ε * X + 2 * δ_sh →
      (roles.V_pref ∩ apInterval lo hi 2 1).card ≤ P_full)
    (hhalf_gate :
      let X : ℝ := poolMaximum n
      ((2 * n - 1 : ℕ) : ℝ) ≤
        ((ε / 2) * X - (1036 / 125 : ℝ) * Real.sqrt X) / Real.log X -
          ((4 * J_max * (24 + 3 * n) + P_half : ℕ) : ℝ))
    (hfull_gate :
      let X : ℝ := poolMaximum n
      ((3 * n + 1 : ℕ) : ℝ) ≤
        (2 * (ε * X) - (1036 / 125 : ℝ) * Real.sqrt X) / Real.log X -
          ((4 * J_max * (24 + 3 * n) + P_full + (2 * n - 1) : ℕ) : ℝ)) :
    Nonempty (FC2KCompletedWitness n P qCert corrLo maxHi J_max W_ord W_diag N_bins δ ε μ_lo μ_hi prof roles) := by
  let X : ℝ := poolMaximum n
  let m : ℝ := fc2kPoolMean n
  have hX_pos : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  let L := 24 * P + 24 * roles.J + 2 * W_diag
  have hJ_le := roles.hJ_le
  have hs : 2 * L + 1 ≤ n := by dsimp [L]; omega
  have hL : 3 ≤ L := by dsimp [L]; omega
  let choice := fc2kDiagChoice L
  -- Step 1: Place rectangles
  let a₀ : Cell n ≃ Fin (n * n) := Fintype.equivOfCardEq (by simp [Cell])
  obtain ⟨a₁, hrect_a₁, _⟩ :=
    place_distinct_pool_entries_preserving a₀ (packedRectangleCorner hs choice) roles.rectVal ∅
      (packedRectangleCorner_injective hs choice) roles.hrect_inj (by simp) (by simp)
  let reserved := packedRectangleSupport hs choice
  -- Step 2: Obtain expander `p` and install row + col networks
  obtain ⟨p, hderange, hexp⟩ := fc2k_permutation_expander_exists hn
  let S := P + roles.J + W_ord
  let perms := bridgeRepeatedPermutations S p
  have hlen_p : perms.length = S * 3 := bridgeRepeatedPermutations_length p
  have hder : ∀ π ∈ perms, ∀ v, π v ≠ v := bridgeRepeatedPermutations_derange p hderange
  let rv (x : Fin perms.length × (Fin n × Bool)) : pool n := roles.rowVal (Fin.cast hlen_p x.1, x.2)
  let cv (x : Fin perms.length × (Fin n × Bool)) : pool n := roles.colVal (Fin.cast hlen_p x.1, x.2)
  let rg (i : Fin perms.length) (e : Fin n) : ℕ := roles.ordGap (Fin.cast hlen_p i) e
  have hrinj : Function.Injective rv := fun x y h => by
    obtain ⟨h1, h2⟩ := Prod.mk.inj (roles.hrow_inj h)
    exact Prod.ext (Fin.cast_injective hlen_p h1) h2
  have hcinj : Function.Injective cv := fun x y h => by
    obtain ⟨h1, h2⟩ := Prod.mk.inj (roles.hcol_inj h)
    exact Prod.ext (Fin.cast_injective hlen_p h1) h2
  have hsep : ∀ x y, (rv x).val ≠ (cv y).val := fun x y => roles.hrow_ne_col _ _
  have hravoid : ∀ x z, z ∈ reserved → (rv x).val ≠ entry a₁ z := by
    intro x z hz heq
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
    rw [hrect_a₁ y] at heq
    exact roles.hrow_ne_rect _ y heq
  have hcavoid : ∀ x z, z ∈ reserved → (cv x).val ≠ entry a₁ z := by
    intro x z hz heq
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
    rw [hrect_a₁ y] at heq
    exact roles.hcol_ne_rect _ y heq
  have hrgap : ∀ i e, (rv (i, (e, true))).val = (rv (i, (e, false))).val + rg i e :=
    fun i e => roles.hrow_gap (Fin.cast hlen_p i) e
  have hcgap : ∀ i e, (cv (i, (e, true))).val = (cv (i, (e, false))).val + rg i e :=
    fun i e => roles.hcol_gap (Fin.cast hlen_p i) e
  have hcap : 4 * (2 + 2 * perms.length + 2 * perms.length) + 8 < n := by
    rw [hlen_p]; dsimp [S]; omega
  obtain ⟨rows, cols, hrlen, hclen, a, hrmap, hcmap, hr, hc, hdis_rc,
      hrowsafe, hcolsafe, hrvalues, hcvalues, hrphysical, hcphysical, hfixed_res,
      hrow_layer_cards, hcol_layer_cards, _, _⟩ :=
    LayerPacking.pack_and_install_two_networks perms perms reserved hder hder
      (packedRectangleSupport_row_load hs choice) (packedRectangleSupport_column_load hs choice)
      hcap a₁ rv cv hrinj hcinj hsep hravoid hcavoid rg rg hrgap hcgap
  have hrS : rows.length = S * 3 := hrlen.trans hlen_p
  have hcS : cols.length = S * 3 := hclen.trans hlen_p
  have hrect_a : ∀ x : Fin L × Fin 4, entry a (packedRectangleCorner hs choice x) = (roles.rectVal x).val := by
    intro x
    rw [hfixed_res _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩), hrect_a₁ x]
  have hrow_a : ∀ x : Fin rows.length × (Fin n × Bool),
      entry a (LayerPacking.sequenceCell rows x) = (roles.rowVal (Fin.cast hrS x.1, x.2)).val := by
    intro x; simpa [rv, hrS] using hrvalues x
  have hcol_a : ∀ x : Fin cols.length × (Fin n × Bool),
      entry a (LayerPacking.sequenceCell cols x).swap = (roles.colVal (Fin.cast hcS x.1, x.2)).val := by
    intro x; simpa [cv, hcS] using hcvalues x
  -- Step 3: Exact `full` cardinality, image decomposition, and `μ₀` bounds
  let full := reserved ∪ LayerPacking.layersSupport rows ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport cols)
  have hdis_res_r : Disjoint reserved (LayerPacking.layersSupport rows) := hr.reserved_disjoint
  have hdis_res_c : Disjoint (reserved ∪ LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
    apply Finset.disjoint_left.mpr; intro z hz12 hzc
    rcases Finset.mem_union.mp hz12 with hzr | hzl
    · exact (hcolsafe z hzc).1 hzr
    · exact Finset.disjoint_left.mp hdis_rc hzl hzc
  have hres_card : reserved.card = 4 * L := by
    dsimp [reserved, packedRectangleSupport]
    rw [Finset.card_image_of_injective _ (packedRectangleCorner_injective hs choice)]
    simp [mul_comm]
  obtain ⟨hr_card, hc_card⟩ := packedLayers_support_cards hr hc
  have hfull_card : full.card = 12 * P * (n + 8) + 12 * roles.J * (n + 8) + 8 * W_diag + 12 * W_ord * n := by
    dsimp [full]
    rw [Finset.card_union_of_disjoint hdis_res_c, Finset.card_union_of_disjoint hdis_res_r,
      hres_card, hr_card, hc_card, hrS, hcS]
    dsimp [L, S]
    ring
  have hres_le : 4 * full.card ≤ n * n := by
    rw [hfull_card]
    have : 12 * roles.J * (n + 8) ≤ 12 * J_max * (n + 8) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 12 hJ_le)
    omega
  have hfull_image : full.image (entry a) = roles.V_pref ∪ roles.V_br ∪ roles.V_wide := by
    dsimp [full]
    rw [Finset.image_union, Finset.image_union]
    have him1 : reserved.image (entry a) = Finset.univ.image (fun x => (roles.rectVal x).val) := by
      dsimp [reserved, packedRectangleSupport]
      rw [Finset.image_image]
      apply Finset.image_congr; intro x _; exact hrect_a x
    have him2 : (LayerPacking.layersSupport rows).image (entry a) =
        Finset.univ.image (fun x => (roles.rowVal x).val) := by
      rw [layersSupport_eq_image_sequenceCell rows, Finset.image_image]
      ext v; simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply, hrow_a]
      exact ⟨fun ⟨x, hx⟩ => ⟨(Fin.cast hrS x.1, x.2), hx⟩,
        fun ⟨y, hy⟩ => ⟨(Fin.cast hrS.symm y.1, y.2), by simpa using hy⟩⟩
    have him3 : (LayerPacking.transposeCells (LayerPacking.layersSupport cols)).image (entry a) =
        Finset.univ.image (fun x => (roles.colVal x).val) := by
      rw [transposeCells_layersSupport_eq_image cols, Finset.image_image]
      ext v; simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply, hcol_a]
      exact ⟨fun ⟨x, hx⟩ => ⟨(Fin.cast hcS x.1, x.2), hx⟩,
        fun ⟨y, hy⟩ => ⟨(Fin.cast hcS.symm y.1, y.2), by simpa using hy⟩⟩
    rw [him1, him2, him3, roles.hrole_union]
  have hfull_sum : (∑ z ∈ full, (entry a z : ℝ)) =
      (∑ x, ((roles.rectVal x).val : ℝ)) + (∑ x, ((roles.rowVal x).val : ℝ)) +
      (∑ x, ((roles.colVal x).val : ℝ)) := by
    dsimp [full]
    rw [Finset.sum_union hdis_res_c, Finset.sum_union hdis_res_r]
    have hs1 : (∑ z ∈ reserved, (entry a z : ℝ)) = ∑ x, ((roles.rectVal x).val : ℝ) := by
      dsimp [reserved, packedRectangleSupport]
      rw [Finset.sum_image (fun x _ y _ h => packedRectangleCorner_injective hs choice h)]
      apply Finset.sum_congr rfl; intro x _; rw [hrect_a x]
    have hs2 : (∑ z ∈ LayerPacking.layersSupport rows, (entry a z : ℝ)) =
        ∑ x, ((roles.rowVal x).val : ℝ) := by
      rw [layersSupport_eq_image_sequenceCell rows,
        Finset.sum_image (fun x _ y _ h => hr.sequenceCell_injective h)]
      let eR : (Fin rows.length × (Fin n × Bool)) ≃ (Fin (S * 3) × (Fin n × Bool)) :=
        Equiv.prodCongr (finCongr hrS) (Equiv.refl _)
      rw [← Equiv.sum_comp eR]
      apply Finset.sum_congr rfl; intro x _; rw [hrow_a x]; rfl
    have hs3 : (∑ z ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols), (entry a z : ℝ)) =
        ∑ x, ((roles.colVal x).val : ℝ) := by
      have hc_inj : Function.Injective (fun x => (LayerPacking.sequenceCell cols x).swap) :=
        Prod.swap_injective.comp hc.sequenceCell_injective
      rw [transposeCells_layersSupport_eq_image cols, Finset.sum_image (fun x _ y _ h => hc_inj h)]
      let eC : (Fin cols.length × (Fin n × Bool)) ≃ (Fin (S * 3) × (Fin n × Bool)) :=
        Equiv.prodCongr (finCongr hcS) (Equiv.refl _)
      rw [← Equiv.sum_comp eC]
      apply Finset.sum_congr rfl; intro x _; rw [hcol_a x]; rfl
    rw [hs1, hs2, hs3]
  let μ₀ := centralEntriesMean (actualUnusedPool a full) centralPoolValue
  have hunused_card : (actualUnusedPool a full).card = n * n - full.card := by
    have hc_eq := actualUnusedPool_card n a full
    omega
  have hunused_pos : 0 < (actualUnusedPool a full).card := by
    have : 4 ≤ n * n := by nlinarith
    omega
  have hunused_sum : (∑ v ∈ actualUnusedPool a full, centralPoolValue v) =
      (Lucas.poolTotal n : ℝ) - ∑ z ∈ full, (entry a z : ℝ) := by
    rw [actualUnusedPool, Finset.sum_image (fun x _ y _ h => (entryPool a).injective h)]
    have hexpr : ∀ z : Cell n, centralPoolValue (entryPool a z) = (entry a z : ℝ) := fun _ => rfl
    simp only [hexpr]
    have hsdiff := Finset.sum_sdiff (f := fun z : Cell n => (entry a z : ℝ)) (Finset.subset_univ full)
    have htot : (∑ z : Cell n, (entry a z : ℝ)) = (Lucas.poolTotal n : ℝ) := by
      exact_mod_cast Lucas.placement_total n a
    linarith
  have hμ₀_bounds : μ_lo ≤ μ₀ ∧ μ₀ ≤ μ_hi := by
    have hmb := hμ_bounds roles.J hJ_le
    dsimp only at hmb
    have hN_eq : ((actualUnusedPool a full).card : ℝ) =
        ((n * n - (12 * P * (n + 8) + 12 * roles.J * (n + 8) + 8 * W_diag + 12 * W_ord * n) : ℕ) : ℝ) := by
      rw [hunused_card, hfull_card]
    have hN_pos : (0 : ℝ) < ((actualUnusedPool a full).card : ℝ) := Nat.cast_pos.mpr hunused_pos
    dsimp [μ₀, centralEntriesMean]
    rw [hunused_sum, hfull_sum]
    rw [← hN_eq] at hmb
    exact ⟨(le_div_iff₀ hN_pos).mpr (by linarith [hmb.1, roles.hrole_sum_upper]),
      (div_le_iff₀ hN_pos).mpr (by linarith [hmb.2, roles.hrole_sum_lower])⟩
  -- Step 4: Bound deletions in central windows and invoke `fc2k_central_band_sharp_completion_two_budgets`
  let δ_sh : ℝ := 6 * (ε * X) / ((n * n - 1 : ℕ) : ℝ)
  have hεX_pos : 0 < ε * X := mul_pos hε hX_pos
  have hδ_sh_pos : 0 < δ_sh := by
    have h1 : 1 < n * n := by nlinarith
    have hden : (0 : ℝ) < ((n * n - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    exact div_pos (by positivity) hden
  have hdel_bound : ∀ (lo hi : ℝ) (capP : ℕ),
      μ_lo - ε * X - δ_sh ≤ lo →
      hi ≤ μ_hi + ε * X + δ_sh →
      lo ≤ hi →
      (roles.V_pref ∩ apInterval lo hi 2 1).card ≤ capP →
      (apInterval lo hi 2 1 ∩ full.image (entry a)).card ≤ 4 * J_max * (24 + 3 * n) + capP := by
    intro lo hi capP hlo_ge hhi_le hbc hcapP
    have hlo0 : 0 ≤ lo := by linarith [hcent_in_pool.1]
    rw [hfull_image]
    have hw_empty : apInterval lo hi 2 1 ∩ roles.V_wide = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨hvI, hvW⟩ := Finset.mem_inter.mp hv
      have hmem := (mem_apInterval_iff lo hi 2 1 hlo0 (hlo0.trans hbc) v).mp hvI
      rcases roles.hV_wide_out v hvW with hL | hR
      · linarith [hwide_sep_cent.1, hlo_ge, hmem.2.1, hL]
      · linarith [hwide_sep_cent.2, hhi_le, hmem.2.2.1, hR]
    have hsub : apInterval lo hi 2 1 ∩ (roles.V_pref ∪ roles.V_br ∪ roles.V_wide) =
        (roles.V_pref ∩ apInterval lo hi 2 1) ∪ (apInterval lo hi 2 1 ∩ roles.V_br) := by
      rw [Finset.inter_union_distrib_left, Finset.inter_union_distrib_left, hw_empty,
        Finset.union_empty, Finset.inter_comm (apInterval lo hi 2 1) roles.V_pref]
    rw [hsub]
    have hc1 := Finset.card_union_le (roles.V_pref ∩ apInterval lo hi 2 1) (apInterval lo hi 2 1 ∩ roles.V_br)
    have hc2 : (apInterval lo hi 2 1 ∩ roles.V_br).card ≤ 4 * J_max * (24 + 3 * n) :=
      (Finset.card_le_card Finset.inter_subset_right).trans
        (roles.hV_br_card.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hJ_le)))
    omega
  have hload_c : 4 * (2 * (rows.length + cols.length) + 4) ≤ n := by
    rw [hrS, hcS]; dsimp [S]; omega
  obtain ⟨_b_diag, c, _hfixed_b, _hfixed_cb, hfixed_c, hmain_c, hanti_c,
      hrows_c, hcols_c, _, _, _, _⟩ :=
    fc2k_central_band_sharp_completion_two_budgets bmor upper hs hL (by omega) (by omega) hodd choice
      rows cols hr hc hload_c a ε (4 * J_max * (24 + 3 * n) + P_half)
      (4 * J_max * (24 + 3 * n) + P_full) hε hres_le
      (by dsimp only; linarith [hcent_in_pool.1, hμ₀_bounds.1])
      (by dsimp only; linarith [hcent_in_pool.2, hμ₀_bounds.2])
      (hdel_bound (μ₀ - ε * X) (μ₀ - (ε * X) / 2) P_half
        (by linarith [hμ₀_bounds.1, hδ_sh_pos])
        (by linarith [hμ₀_bounds.2, hεX_pos, hδ_sh_pos])
        (by linarith [hεX_pos])
        (hP_half _ _ (by linarith [hμ₀_bounds.1]) (by linarith [hμ₀_bounds.2, hεX_pos])
          (by linarith [hεX_pos]) (by linarith)))
      (hdel_bound (μ₀ + (ε * X) / 2) (μ₀ + ε * X) P_half
        (by linarith [hμ₀_bounds.1, hεX_pos, hδ_sh_pos])
        (by linarith [hμ₀_bounds.2, hδ_sh_pos])
        (by linarith [hεX_pos])
        (hP_half _ _ (by linarith [hμ₀_bounds.1, hεX_pos]) (by linarith [hμ₀_bounds.2])
          (by linarith [hεX_pos]) (by linarith)))
      (hdel_bound (μ₀ - ε * X - δ_sh) (μ₀ + ε * X + δ_sh) P_full
        (by linarith [hμ₀_bounds.1])
        (by linarith [hμ₀_bounds.2])
        (by linarith [hεX_pos, hδ_sh_pos])
        (hP_full _ _ (by linarith [hμ₀_bounds.1]) (by linarith [hμ₀_bounds.2])
          (by linarith [hεX_pos, hδ_sh_pos]) (by linarith)))
      hhalf_gate hfull_gate
  -- Step 5: Assemble `BR`, `BC` on `c`
  let rowGap (i : Fin rows.length) (e : Fin n) : ℕ := roles.ordGap (Fin.cast hrS i) e
  let colGap (i : Fin cols.length) (e : Fin n) : ℕ := roles.ordGap (Fin.cast hcS i) e
  have hrowGap_c : ∀ i e, entry c ((rows.get i).1 e, (rows.get i).2 e) =
      entry c (e, (rows.get i).2 e) + rowGap i e := by
    intro i e
    have hlow : (e, (rows.get i).2 e) ∈ full := Finset.mem_union_left _ (Finset.mem_union_right _
      (LayerPacking.layerSupport_subset (rows.get i) rows (List.get_mem rows i)
        (by simpa [LayerPacking.sequenceCell, LayerPacking.layerCell] using
          LayerPacking.sequenceCell_mem rows i (e, false))))
    have hhigh : ((rows.get i).1 e, (rows.get i).2 e) ∈ full := Finset.mem_union_left _ (Finset.mem_union_right _
      (LayerPacking.layerSupport_subset (rows.get i) rows (List.get_mem rows i)
        (by simpa [LayerPacking.sequenceCell, LayerPacking.layerCell] using
          LayerPacking.sequenceCell_mem rows i (e, true))))
    rw [hfixed_c _ hhigh, hfixed_c _ hlow]
    simpa [rg, rowGap, hrS] using hrphysical i e
  have hcolGap_c : ∀ i e, entry c ((cols.get i).2 e, (cols.get i).1 e) =
      entry c ((cols.get i).2 e, e) + colGap i e := by
    intro i e
    have hlow : ((cols.get i).2 e, e) ∈ full := Finset.mem_union_right _
      (by simpa [layerPairSlot, LayerPacking.sequenceCell, LayerPacking.layerCell] using
        transposedLayerPairSlot_mem cols (i, e) false)
    have hhigh : ((cols.get i).2 e, (cols.get i).1 e) ∈ full := Finset.mem_union_right _
      (by simpa [layerPairSlot, LayerPacking.sequenceCell, LayerPacking.layerCell] using
        transposedLayerPairSlot_mem cols (i, e) true)
    rw [hfixed_c _ hhigh, hfixed_c _ hlow]
    simpa [rg, colGap, hcS] using hcphysical i e
  have hgrid_relabel : ∀ {m_len : ℕ} (hm : m_len = S * 3) (e : Fin 3 × Fin n),
      CompleteEvenGrid (prefixPairBlock S (prefixPhysicalStageSlot hm) e)
        (fun k : Fin m_len × Fin n => roles.ordGap (Fin.cast hm k.1) k.2) (roles.edgeRadius e) := by
    intro m_len hm e
    let srcSet := (Finset.univ : Finset (Fin S)).image
      (fun s => (bridgeStageLayerIndex (r := 3) (J := S) rfl s e.1, e.2))
    let fSub : {x // x ∈ srcSet} → Fin m_len × Fin n :=
      fun x => (Fin.cast hm.symm x.1.1, x.1.2)
    have hfSub_inj : Function.Injective fSub := by
      rintro ⟨⟨i₁, e₁⟩, _⟩ ⟨⟨i₂, e₂⟩, _⟩ h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      exact Subtype.ext (Prod.ext (Fin.cast_injective hm.symm h1) h2)
    have hrel := completeEvenGrid_finite_relabel srcSet (fun k => roles.ordGap k.1 k.2)
      (roles.edgeRadius e) fSub hfSub_inj
      (fun k => roles.ordGap (Fin.cast hm k.1) k.2)
      (by rintro ⟨⟨i, e'⟩, _⟩; simp [fSub]) (roles.hedge_grid e)
    have hset_eq : srcSet.attach.image fSub = prefixPairBlock S (prefixPhysicalStageSlot hm) e := by
      ext ⟨i, e'⟩
      simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, srcSet,
        prefixPairBlock, prefixPhysicalStageSlot, Finset.mem_univ, fSub]
      constructor
      · rintro ⟨⟨i₀, e₀⟩, ⟨s, hs0⟩, heq⟩
        refine ⟨s, ?_⟩
        rw [← heq, ← hs0]
        ext <;> simp [bridgeStageLayerIndex]
      · rintro ⟨s, hs0⟩
        refine ⟨(bridgeStageLayerIndex rfl s e.1, e.2), ⟨s, rfl⟩, ?_⟩
        rw [← hs0]
        ext <;> simp [bridgeStageLayerIndex]
    rw [hset_eq] at hrel
    exact hrel
  let BR := fc2kInstalledCenteredNetwork rows hrS p hrmap
    (hr.rowPairs c rowGap hrowGap_c) (fun _ => rfl) (fun _ => rfl)
    roles.edgeRadius (fun e => hgrid_relabel hrS e)
  let BC := fc2kInstalledCenteredNetwork cols hcS p hcmap
    (hc.columnPairs c colGap hcolGap_c) (fun _ => rfl) (fun _ => rfl)
    roles.edgeRadius (fun e => hgrid_relabel hcS e)
  -- Step 6: Prove `hmain_diff_c`
  have hmain_inter : mainCells n ∩ full =
      (Finset.univ.filter (fun t : Fin L => choice t = true)).image
        (fun t => packedRectangleCorner hs choice (t, 0)) := by
    have h1 : mainCells n ∩ full = packedRectangleSupport hs choice ∩ mainCells n := by
      ext z; simp only [full, Finset.mem_inter, Finset.mem_union]
      have hr_off := fun hz => (hrowsafe z hz).2.1
      have hc_off := fun hz => (hcolsafe z hz).2.1
      tauto
    have h2 := active_rectangle_main_cells hs hL choice Finset.univ
    have hact : activeRectangleSupport hs choice Finset.univ = packedRectangleSupport hs choice := by
      simp [activeRectangleSupport, packedRectangleSupport]
    rw [hact] at h2
    exact h1.trans h2
  have hanti_inter : antiCells n ∩ full =
      (Finset.univ.filter (fun t : Fin L => choice t = false)).image
        (fun t => packedRectangleCorner hs choice (t, 0)) := by
    have h1 : antiCells n ∩ full = packedRectangleSupport hs choice ∩ antiCells n := by
      ext z; simp only [full, Finset.mem_inter, Finset.mem_union]
      have hr_off := fun hz => (hrowsafe z hz).2.2
      have hc_off := fun hz => (hcolsafe z hz).2.2
      tauto
    have h2 := active_rectangle_anti_cells hs hL choice Finset.univ
    have hact : activeRectangleSupport hs choice Finset.univ = packedRectangleSupport hs choice := by
      simp [activeRectangleSupport, packedRectangleSupport]
    rw [hact] at h2
    exact h1.trans h2
  have hcorner0_inj : Function.Injective (fun t : Fin L => packedRectangleCorner hs choice (t, 0)) :=
    fun t₁ t₂ h => congrArg Prod.fst (packedRectangleCorner_injective hs choice h)
  have hm_sdiff_card : (mainCells n \ full).card = n - (12 * P + 12 * roles.J + W_diag) := by
    let K_h := 12 * P + 12 * roles.J + W_diag
    have hL_2K : L = 2 * K_h := by dsimp [L, K_h]; ring
    let eqv : Fin L ≃ Fin (2 * K_h) := finCongr hL_2K
    obtain ⟨hbT, _⟩ := fc2kDiagChoice_balance K_h
    have hm_card : (mainCells n ∩ full).card = K_h := by
      rw [hmain_inter, Finset.card_image_of_injective _ hcorner0_inj]
      have heq_f : ((Finset.univ : Finset (Fin L)).filter (fun t => choice t = true)).card =
          ((Finset.univ : Finset (Fin (2 * K_h))).filter (fun t => fc2kDiagChoice (2 * K_h) t = true)).card := by
        rw [← Finset.card_map eqv.toEmbedding]
        congr 1; ext x
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coeFn_mk]
        exact ⟨fun ⟨t, ht, htx⟩ => by rw [← htx]; simpa [choice, fc2kDiagChoice, eqv] using ht,
          fun hx => ⟨eqv.symm x, by simpa [choice, fc2kDiagChoice, eqv] using hx, eqv.apply_symm_apply x⟩⟩
      exact heq_f.trans hbT
    have hms := Finset.card_sdiff_add_card_inter (mainCells n) full
    rw [hm_card, mainCells_card] at hms
    dsimp [K_h] at hms
    omega
  have hdiag_sdiff_eq : (mainCells n \ full).card = (antiCells n \ full).card := by
    let K_h := 12 * P + 12 * roles.J + W_diag
    have hL_2K : L = 2 * K_h := by dsimp [L, K_h]; ring
    let eqv : Fin L ≃ Fin (2 * K_h) := finCongr hL_2K
    obtain ⟨_, hbF⟩ := fc2kDiagChoice_balance K_h
    have ha_card : (antiCells n ∩ full).card = K_h := by
      rw [hanti_inter, Finset.card_image_of_injective _ hcorner0_inj]
      have heq_f : ((Finset.univ : Finset (Fin L)).filter (fun t => choice t = false)).card =
          ((Finset.univ : Finset (Fin (2 * K_h))).filter (fun t => fc2kDiagChoice (2 * K_h) t = false)).card := by
        rw [← Finset.card_map eqv.toEmbedding]
        congr 1; ext x
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coeFn_mk]
        exact ⟨fun ⟨t, ht, htx⟩ => by rw [← htx]; simpa [choice, fc2kDiagChoice, eqv] using ht,
          fun hx => ⟨eqv.symm x, by simpa [choice, fc2kDiagChoice, eqv] using hx, eqv.apply_symm_apply x⟩⟩
      exact heq_f.trans hbF
    have has := Finset.card_sdiff_add_card_inter (antiCells n) full
    rw [ha_card, antiCells_card] at has
    rw [hm_sdiff_card]
    dsimp [K_h] at has
    omega
  have hmain_lo_c :
      ((n - (12 * P + 12 * J_max + W_diag) : ℕ) : ℝ) * μ_lo - 2 * ε * X ≤ (mainSum c : ℝ) := by
    have hm_err := (abs_le.mp hmain_c).1
    have hsum_nn : 0 ≤ ∑ z ∈ mainCells n ∩ full, (entry a z : ℝ) :=
      Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hcard_ge : ((n - (12 * P + 12 * J_max + W_diag) : ℕ) : ℝ) ≤ ((mainCells n \ full).card : ℝ) := by
      exact_mod_cast (show n - (12 * P + 12 * J_max + W_diag) ≤ (mainCells n \ full).card by
        rw [hm_sdiff_card]; omega)
    have hμ_lo_nn : 0 ≤ μ_lo := by
      dsimp only at hcent_in_pool
      linarith [hcent_in_pool.1, hεX_pos, hδ_sh_pos]
    have hprod_le : ((n - (12 * P + 12 * J_max + W_diag) : ℕ) : ℝ) * μ_lo ≤
        ((mainCells n \ full).card : ℝ) * μ₀ :=
      mul_le_mul hcard_ge hμ₀_bounds.1 hμ_lo_nn (Nat.cast_nonneg _)
    linarith
  have hmain_diff_c : |(mainSum c : ℝ) + (roles.Rm : ℝ) / 2 -
      ((antiSum c : ℝ) + (roles.Ra : ℝ) / 2)| ≤
      ((prof.totalSpanWords * 49152 : ℕ) : ℝ) +
      (9 / 25 : ℝ) * (roles.J : ℝ) * X +
      (W_diag : ℝ) * δ * X +
      (401 / 100 : ℝ) * ε * X := by
    have hm_sum : (∑ z ∈ mainCells n ∩ full, (entry a z : ℝ)) + (roles.Rm : ℝ) / 2 =
        ∑ t ∈ Finset.univ.filter (fun t : Fin L => decide (t.val % 2 = 0) = true),
          (((roles.rectVal (t, 0)).val : ℝ) + (roles.rectGap t : ℝ) / 2) := by
      have hflt : Finset.univ.filter (fun t : Fin L => choice t = true) =
          Finset.univ.filter (fun t : Fin L => decide (t.val % 2 = 0) = true) := by
        ext t; simp [choice, fc2kDiagChoice]
      rw [hmain_inter, Finset.sum_image (fun x _ y _ h => hcorner0_inj h), hflt, roles.hRm_sum]
      push_cast; rw [Finset.sum_div, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro t _; rw [hrect_a (t, 0)]
    have ha_sum : (∑ z ∈ antiCells n ∩ full, (entry a z : ℝ)) + (roles.Ra : ℝ) / 2 =
        ∑ t ∈ Finset.univ.filter (fun t : Fin L => decide (t.val % 2 = 0) = false),
          (((roles.rectVal (t, 0)).val : ℝ) + (roles.rectGap t : ℝ) / 2) := by
      have hflt : Finset.univ.filter (fun t : Fin L => choice t = false) =
          Finset.univ.filter (fun t : Fin L => decide (t.val % 2 = 0) = false) := by
        ext t; simp [choice, fc2kDiagChoice]
      rw [hanti_inter, Finset.sum_image (fun x _ y _ h => hcorner0_inj h), hflt, roles.hRa_sum]
      push_cast; rw [Finset.sum_div, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro t _; rw [hrect_a (t, 0)]
    have hm_err := abs_le.mp hmain_c
    have ha_err := abs_le.mp hanti_c
    have hmid_err := abs_le.mp roles.hdiag_mid_diff
    rw [hdiag_sdiff_eq] at hm_err
    rw [abs_le]
    exact ⟨by linarith [hm_err.1, ha_err.2, hmid_err.1, hm_sum, ha_sum],
      by linarith [hm_err.2, ha_err.1, hmid_err.2, hm_sum, ha_sum]⟩
  -- Step 7: Define `M_row_ideal`, `M_col_ideal` and prove sum + approx + pairwise width
  let R_div (r : Fin n) : ℝ :=
    (1 / 2 : ℝ) * ∑ e : Fin 3 × Fin n,
      (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (roles.edgeRadius e : ℤ)) e r : ℝ)
  let M_row_ideal (r : Fin n) : ℝ :=
    (∑ z ∈ rowCells r ∩ full, (entry a z : ℝ)) + ((rowCells r \ full).card : ℝ) * μ₀ + R_div r
  let M_col_ideal (col : Fin n) : ℝ :=
    (∑ z ∈ columnCells col ∩ full, (entry a z : ℝ)) + ((columnCells col \ full).card : ℝ) * μ₀ + R_div col
  have hdiv_sum_zero : ∑ r : Fin n, R_div r = 0 := by
    dsimp [R_div]
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hper_e : ∀ e : Fin 3 × Fin n,
        (∑ r : Fin n, (edgeTransfer Prod.snd (fun x : Fin 3 × Fin n => p x.1 x.2)
          (fun x => (roles.edgeRadius x : ℤ)) e r : ℝ)) = 0 := by
      intro e
      have hcast_e : ∀ r : Fin n,
          (edgeTransfer Prod.snd (fun x : Fin 3 × Fin n => p x.1 x.2)
            (fun x => (roles.edgeRadius x : ℤ)) e r : ℝ) =
          (if e.2 = r then (roles.edgeRadius e : ℝ) else 0) -
          (if p e.1 e.2 = r then (roles.edgeRadius e : ℝ) else 0) := by
        intro r; unfold edgeTransfer; split_ifs <;> push_cast <;> ring
      simp [hcast_e, Finset.sum_sub_distrib]
    simp [hper_e]
  have hrow_part_sum : ∀ (f : Cell n → ℝ) (T : Finset (Cell n)),
      (∑ r : Fin n, ∑ z ∈ rowCells r ∩ T, f z) = ∑ z ∈ T, f z := by
    intro f T
    have hdis_r : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin n))) (fun r => rowCells r ∩ T) := by
      intro r₁ _ r₂ _ hne
      apply Finset.disjoint_left.mpr; intro z hz1 hz2
      have h1 := mem_rowCells r₁ z |>.mp (Finset.mem_inter.mp hz1).1
      have h2 := mem_rowCells r₂ z |>.mp (Finset.mem_inter.mp hz2).1
      exact hne (h1.symm.trans h2)
    have hun_r : Finset.univ.biUnion (fun r => rowCells r ∩ T) = T := by
      ext z; simp
    rw [← Finset.sum_biUnion hdis_r, hun_r]
  have hcol_part_sum : ∀ (f : Cell n → ℝ) (T : Finset (Cell n)),
      (∑ col : Fin n, ∑ z ∈ columnCells col ∩ T, f z) = ∑ z ∈ T, f z := by
    intro f T
    have hdis_c : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin n))) (fun col => columnCells col ∩ T) := by
      intro c₁ _ c₂ _ hne
      apply Finset.disjoint_left.mpr; intro z hz1 hz2
      have h1 := mem_columnCells c₁ z |>.mp (Finset.mem_inter.mp hz1).1
      have h2 := mem_columnCells c₂ z |>.mp (Finset.mem_inter.mp hz2).1
      exact hne (h1.symm.trans h2)
    have hun_c : Finset.univ.biUnion (fun col => columnCells col ∩ T) = T := by
      ext z; simp
    rw [← Finset.sum_biUnion hdis_c, hun_c]
  have hμ₀_mul_eq : ((Finset.univ \ full).card : ℝ) * μ₀ =
      (Lucas.poolTotal n : ℝ) - ∑ z ∈ full, (entry a z : ℝ) := by
    have hcard_eq : (Finset.univ \ full).card = (actualUnusedPool a full).card := by
      rw [actualUnusedPool, Finset.card_image_of_injective _ (entryPool a).injective]
    have hN_ne : ((actualUnusedPool a full).card : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr hunused_pos)
    rw [hcard_eq]
    dsimp [μ₀, centralEntriesMean]
    rw [hunused_sum, mul_div_cancel₀ _ hN_ne]
  have hrow_ideal_sum : ∑ r : Fin n, M_row_ideal r = (Lucas.poolTotal n : ℝ) := by
    dsimp [M_row_ideal]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hdiv_sum_zero, add_zero,
      hrow_part_sum _ full, ← Finset.sum_mul]
    have hcards : (∑ r : Fin n, ((rowCells r \ full).card : ℝ)) = ((Finset.univ \ full).card : ℝ) := by
      have heq_sd : ∀ r : Fin n, ((rowCells r \ full).card : ℝ) = ∑ z ∈ rowCells r ∩ (Finset.univ \ full), (1 : ℝ) := by
        intro r
        have hs : rowCells r \ full = rowCells r ∩ (Finset.univ \ full) := by ext z; simp
        rw [hs, Finset.sum_const, nsmul_eq_mul, mul_one]
      simp only [heq_sd]
      rw [hrow_part_sum _ (Finset.univ \ full), Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcards, hμ₀_mul_eq]
    ring
  have hcol_ideal_sum : ∑ col : Fin n, M_col_ideal col = (Lucas.poolTotal n : ℝ) := by
    dsimp [M_col_ideal]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hdiv_sum_zero, add_zero,
      hcol_part_sum _ full, ← Finset.sum_mul]
    have hcards : (∑ col : Fin n, ((columnCells col \ full).card : ℝ)) = ((Finset.univ \ full).card : ℝ) := by
      have heq_sd : ∀ col : Fin n, ((columnCells col \ full).card : ℝ) = ∑ z ∈ columnCells col ∩ (Finset.univ \ full), (1 : ℝ) := by
        intro col
        have hs : columnCells col \ full = columnCells col ∩ (Finset.univ \ full) := by ext z; simp
        rw [hs, Finset.sum_const, nsmul_eq_mul, mul_one]
      simp only [heq_sd]
      rw [hcol_part_sum _ (Finset.univ \ full), Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcards, hμ₀_mul_eq]
    ring
  -- Pairwise width of `M_row_ideal` and `M_col_ideal`
  let loB0 := min (2 * (corrLo : ℝ)) (min ((197 / 200 : ℝ) * X) (2 * m - δ * X))
  let hiB0 := max (2 * (maxHi : ℝ)) (max ((203 / 200 : ℝ) * X) (2 * m + δ * X))
  have hrow_decomp : ∀ r : Fin n,
      ∃ rectTerm : ℝ,
        min loB0 (2 * μ₀) ≤ rectTerm ∧ rectTerm ≤ max hiB0 (2 * μ₀) ∧
        M_row_ideal r = ((n - 12 * S - 2 : ℕ) : ℝ) * μ₀ + rectTerm +
          ∑ s : Fin S, ∑ l : Fin 3,
            (let idx := bridgeStageLayerIndex (r := 3) (J := S) rfl s l
             let gc := (cols.get (bridgeStageLayerIndex hcS s l)).2
             ((((roles.rowVal (idx, (r, false))).val + (roles.rowVal (idx, (r, true))).val : ℕ) : ℝ) +
              (((roles.rowVal (idx, ((p l).symm r, false))).val + (roles.rowVal (idx, ((p l).symm r, true))).val : ℕ) : ℝ)) / 2 +
             ((((roles.colVal (idx, (gc.symm r, false))).val + (roles.colVal (idx, (gc.symm r, true))).val : ℕ) : ℝ) +
              (((roles.colVal (idx, (gc.symm r, false))).val + (roles.colVal (idx, (gc.symm r, true))).val : ℕ) : ℝ)) / 2) := by
    intro r
    have hrect_b := fc2k_row_rect_term_bounds hs choice a roles.rectVal hrect_a
      (μ₀ := μ₀) roles.hrect_pair_bounds r
    have hd1 : Disjoint (rowCells r ∩ reserved) (rowCells r ∩ LayerPacking.layersSupport rows) :=
      hdis_res_r.mono Finset.inter_subset_right Finset.inter_subset_right
    have hd2 : Disjoint ((rowCells r ∩ reserved) ∪ (rowCells r ∩ LayerPacking.layersSupport rows))
        (rowCells r ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
      rw [← Finset.inter_union_distrib_left]
      exact hdis_res_c.mono Finset.inter_subset_right Finset.inter_subset_right
    have hsplit_r : rowCells r ∩ full = (rowCells r ∩ reserved) ∪
        (rowCells r ∩ LayerPacking.layersSupport rows) ∪
        (rowCells r ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
      dsimp [full]; rw [Finset.inter_union_distrib_left, Finset.inter_union_distrib_left]
    have hcard_r_layers : (rowCells r ∩ LayerPacking.layersSupport rows).card = 6 * S ∧
        (rowCells r ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols)).card = 6 * S := by
      have heq1 : rowCells r ∩ LayerPacking.layersSupport rows =
          (LayerPacking.layersSupport rows).filter (fun z => z.1 = r) := by ext z; simp [and_comm]
      have heq2 : rowCells r ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols) =
          (LayerPacking.transposeCells (LayerPacking.layersSupport cols)).filter (fun z => z.1 = r) := by
        ext z; simp [and_comm]
      rw [heq1, heq2, (hrow_layer_cards r).1, (hrow_layer_cards r).2, hlen_p]
      exact ⟨by ring, by ring⟩
    have hsdiff_card : (rowCells r \ full).card = (n - 12 * S - 2) + (2 - (rowCells r ∩ reserved).card) := by
      have htot_r := Finset.card_sdiff_add_card_inter (rowCells r) full
      have hrc_n : (rowCells r).card = n := by
        dsimp [rowCells]; rw [Finset.card_image_of_injective _ (fun a b h => congrArg Prod.snd h)]; simp
      have hfull_r : (rowCells r ∩ full).card = (rowCells r ∩ reserved).card + 12 * S := by
        rw [hsplit_r, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
          hcard_r_layers.1, hcard_r_layers.2]; ring
      have hq2 : (rowCells r ∩ reserved).card ≤ 2 := hrect_b.1
      have h12S : 12 * S + 2 ≤ n := by dsimp [S]; omega
      omega
    have hord_eq := fc2k_row_ord_midpoint_eq p rows cols hrS hcS hrmap hr hc a
      roles.rowVal roles.colVal roles.ordGap roles.hrow_gap hrow_a hcol_a
      roles.edgeRadius (fun e => (roles.hedge_sum e).symm) r
    refine ⟨(∑ z ∈ rowCells r ∩ reserved, (entry a z : ℝ)) + ((2 - (rowCells r ∩ reserved).card : ℕ) : ℝ) * μ₀,
      hrect_b.2.1, hrect_b.2.2, ?_⟩
    dsimp only [M_row_ideal, R_div]
    rw [hsplit_r, Finset.sum_union hd2, Finset.sum_union hd1, hsdiff_card, Nat.cast_add]
    calc (∑ x ∈ rowCells r ∩ reserved, (entry a x : ℝ)) +
           (∑ x ∈ rowCells r ∩ LayerPacking.layersSupport rows, (entry a x : ℝ)) +
           (∑ x ∈ rowCells r ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols), (entry a x : ℝ)) +
           (((n - 12 * S - 2 : ℕ) : ℝ) + ((2 - (rowCells r ∩ reserved).card : ℕ) : ℝ)) * μ₀ +
           (1 / 2 : ℝ) * ∑ e : Fin 3 × Fin n,
             (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (roles.edgeRadius e : ℤ)) e r : ℝ)
        = ((n - 12 * S - 2 : ℕ) : ℝ) * μ₀ +
          ((∑ z ∈ rowCells r ∩ reserved, (entry a z : ℝ)) + ((2 - (rowCells r ∩ reserved).card : ℕ) : ℝ) * μ₀) +
          ((∑ z ∈ rowCells r ∩ LayerPacking.layersSupport rows, (entry a z : ℝ)) +
           (∑ z ∈ rowCells r ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols), (entry a z : ℝ)) +
           (1 / 2 : ℝ) * ∑ e : Fin 3 × Fin n,
             (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (roles.edgeRadius e : ℤ)) e r : ℝ)) := by ring
      _ = _ := by rw [hord_eq]
  have hcol_pair_all : ∀ t : Fin L,
      loB0 ≤ (((roles.rectVal (t, 0)).val + (roles.rectVal (t, 2)).val : ℕ) : ℝ) ∧
      (((roles.rectVal (t, 0)).val + (roles.rectVal (t, 2)).val : ℕ) : ℝ) ≤ hiB0 ∧
      loB0 ≤ (((roles.rectVal (t, 1)).val + (roles.rectVal (t, 3)).val : ℕ) : ℝ) ∧
      (((roles.rectVal (t, 1)).val + (roles.rectVal (t, 3)).val : ℕ) : ℝ) ≤ hiB0 := by
    intro t
    have hg := roles.hrect_gap t
    have hp := roles.hrect_pair_bounds t
    exact fc2k_rect_col_pair_bounds hg.2.2.1 hg.2.2.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  have hcol_decomp : ∀ col : Fin n,
      ∃ rectTerm : ℝ,
        min loB0 (2 * μ₀) ≤ rectTerm ∧ rectTerm ≤ max hiB0 (2 * μ₀) ∧
        M_col_ideal col = ((n - 12 * S - 2 : ℕ) : ℝ) * μ₀ + rectTerm +
          ∑ s : Fin S, ∑ l : Fin 3,
            (let idx := bridgeStageLayerIndex (r := 3) (J := S) rfl s l
             let gr := (rows.get (bridgeStageLayerIndex hrS s l)).2
             ((((roles.rowVal (idx, (gr.symm col, false))).val + (roles.rowVal (idx, (gr.symm col, true))).val : ℕ) : ℝ) +
              (((roles.rowVal (idx, (gr.symm col, false))).val + (roles.rowVal (idx, (gr.symm col, true))).val : ℕ) : ℝ)) / 2 +
             ((((roles.colVal (idx, (col, false))).val + (roles.colVal (idx, (col, true))).val : ℕ) : ℝ) +
              (((roles.colVal (idx, ((p l).symm col, false))).val + (roles.colVal (idx, ((p l).symm col, true))).val : ℕ) : ℝ)) / 2) := by
    intro col
    have hrect_b := fc2k_col_rect_term_bounds hs choice a roles.rectVal hrect_a
      (μ₀ := μ₀) hcol_pair_all col
    have hd1 : Disjoint (columnCells col ∩ reserved) (columnCells col ∩ LayerPacking.layersSupport rows) :=
      hdis_res_r.mono Finset.inter_subset_right Finset.inter_subset_right
    have hd2 : Disjoint ((columnCells col ∩ reserved) ∪ (columnCells col ∩ LayerPacking.layersSupport rows))
        (columnCells col ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
      rw [← Finset.inter_union_distrib_left]
      exact hdis_res_c.mono Finset.inter_subset_right Finset.inter_subset_right
    have hsplit_c : columnCells col ∩ full = (columnCells col ∩ reserved) ∪
        (columnCells col ∩ LayerPacking.layersSupport rows) ∪
        (columnCells col ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
      dsimp [full]; rw [Finset.inter_union_distrib_left, Finset.inter_union_distrib_left]
    have hcard_c_layers : (columnCells col ∩ LayerPacking.layersSupport rows).card = 6 * S ∧
        (columnCells col ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols)).card = 6 * S := by
      have heq1 : columnCells col ∩ LayerPacking.layersSupport rows =
          (LayerPacking.layersSupport rows).filter (fun z => z.2 = col) := by ext z; simp [and_comm]
      have heq2 : columnCells col ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols) =
          (LayerPacking.transposeCells (LayerPacking.layersSupport cols)).filter (fun z => z.2 = col) := by
        ext z; simp [and_comm]
      rw [heq1, heq2, (hcol_layer_cards col).1, (hcol_layer_cards col).2, hlen_p]
      exact ⟨by ring, by ring⟩
    have hsdiff_card : (columnCells col \ full).card = (n - 12 * S - 2) + (2 - (columnCells col ∩ reserved).card) := by
      have htot_c := Finset.card_sdiff_add_card_inter (columnCells col) full
      have hcc_n : (columnCells col).card = n := by
        dsimp [columnCells]; rw [Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)]; simp
      have hfull_c : (columnCells col ∩ full).card = (columnCells col ∩ reserved).card + 12 * S := by
        rw [hsplit_c, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
          hcard_c_layers.1, hcard_c_layers.2]; ring
      have hq2 : (columnCells col ∩ reserved).card ≤ 2 := hrect_b.1
      have h12S : 12 * S + 2 ≤ n := by dsimp [S]; omega
      omega
    have hord_eq := fc2k_col_ord_midpoint_eq p rows cols hrS hcS hcmap hr hc a
      roles.rowVal roles.colVal roles.ordGap roles.hcol_gap hrow_a hcol_a
      roles.edgeRadius (fun e => (roles.hedge_sum e).symm) col
    refine ⟨(∑ z ∈ columnCells col ∩ reserved, (entry a z : ℝ)) + ((2 - (columnCells col ∩ reserved).card : ℕ) : ℝ) * μ₀,
      hrect_b.2.1, hrect_b.2.2, ?_⟩
    dsimp only [M_col_ideal, R_div]
    rw [hsplit_c, Finset.sum_union hd2, Finset.sum_union hd1, hsdiff_card, Nat.cast_add]
    calc (∑ x ∈ columnCells col ∩ reserved, (entry a x : ℝ)) +
           (∑ x ∈ columnCells col ∩ LayerPacking.layersSupport rows, (entry a x : ℝ)) +
           (∑ x ∈ columnCells col ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols), (entry a x : ℝ)) +
           (((n - 12 * S - 2 : ℕ) : ℝ) + ((2 - (columnCells col ∩ reserved).card : ℕ) : ℝ)) * μ₀ +
           (1 / 2 : ℝ) * ∑ e : Fin 3 × Fin n,
             (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (roles.edgeRadius e : ℤ)) e col : ℝ)
        = ((n - 12 * S - 2 : ℕ) : ℝ) * μ₀ +
          ((∑ z ∈ columnCells col ∩ reserved, (entry a z : ℝ)) + ((2 - (columnCells col ∩ reserved).card : ℕ) : ℝ) * μ₀) +
          ((∑ z ∈ columnCells col ∩ LayerPacking.layersSupport rows, (entry a z : ℝ)) +
           (∑ z ∈ columnCells col ∩ LayerPacking.transposeCells (LayerPacking.layersSupport cols), (entry a z : ℝ)) +
           (1 / 2 : ℝ) * ∑ e : Fin 3 × Fin n,
             (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (roles.edgeRadius e : ℤ)) e col : ℝ)) := by ring
      _ = _ := by rw [hord_eq]
  exact ⟨{
    L := L
    hL_def := rfl
    hs := hs
    hL := hL
    choice := choice
    hchoice := rfl
    p := p
    hderange := hderange
    hexp := hexp
    rows := rows
    cols := cols
    hrS := hrS
    hcS := hcS
    hr := hr
    hc := hc
    a := a
    c := c
    hrect_c := fun x => (hfixed_c _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)))).trans (hrect_a x)
    rowGap := rowGap
    colGap := colGap
    hrowGap_c := hrowGap_c
    hcolGap_c := hcolGap_c
    BR := BR
    BC := BC
    hends := fun _ => ⟨rfl, rfl, rfl, rfl⟩
    hR_rad := fun _ => rfl
    hC_rad := fun _ => rfl
    μ₀ := μ₀
    hμ₀_bounds := hμ₀_bounds
    hmain_diff_c := hmain_diff_c
    hmain_lo_c := hmain_lo_c
    M_row_ideal := M_row_ideal
    M_col_ideal := M_col_ideal
    hrow_ideal_sum := hrow_ideal_sum
    hcol_ideal_sum := hcol_ideal_sum
    hrow_c_approx := fun r => by
      have hr_c := hrows_c r
      dsimp [M_row_ideal, R_div, BR, fc2kInstalledCenteredNetwork]
      have heq_sub : ((rowSum c r : ℝ) + (1 / 2 : ℝ) * ∑ e : Fin 3 × Fin n,
          (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (roles.edgeRadius e : ℤ)) e r : ℝ)) -
          ((∑ z ∈ rowCells r ∩ full, (entry a z : ℝ)) + ((rowCells r \ full).card : ℝ) * μ₀ +
          (1 / 2 : ℝ) * ∑ e : Fin 3 × Fin n,
            (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (roles.edgeRadius e : ℤ)) e r : ℝ)) =
          (rowSum c r : ℝ) - ((∑ z ∈ rowCells r ∩ full, (entry a z : ℝ)) +
            ((rowCells r \ full).card : ℝ) * μ₀) := by ring
      rw [heq_sub]; exact hr_c
    hcol_c_approx := fun col => by
      have hc_c := hcols_c col
      dsimp [M_col_ideal, R_div, BC, fc2kInstalledCenteredNetwork]
      have heq_sub : ((columnSum c col : ℝ) + (1 / 2 : ℝ) * ∑ e : Fin 3 × Fin n,
          (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (roles.edgeRadius e : ℤ)) e col : ℝ)) -
          ((∑ z ∈ columnCells col ∩ full, (entry a z : ℝ)) + ((columnCells col \ full).card : ℝ) * μ₀ +
          (1 / 2 : ℝ) * ∑ e : Fin 3 × Fin n,
            (edgeTransfer Prod.snd (fun e => p e.1 e.2) (fun e => (roles.edgeRadius e : ℤ)) e col : ℝ)) =
          (columnSum c col : ℝ) - ((∑ z ∈ columnCells col ∩ full, (entry a z : ℝ)) +
            ((columnCells col \ full).card : ℝ) * μ₀) := by ring
      rw [heq_sub]; exact hc_c
    hrow_ideal_width := fun r₁ r₂ => by
      obtain ⟨rt₁, hrt1_lo, hrt1_hi, hM₁⟩ := hrow_decomp r₁
      obtain ⟨rt₂, hrt2_lo, hrt2_hi, hM₂⟩ := hrow_decomp r₂
      have hw := roles.hord_stage_width
        (fun _ _ => r₁) (fun _ l => (p l).symm r₁)
        (fun _ _ => r₂) (fun _ l => (p l).symm r₂)
        (fun s l => ((cols.get (bridgeStageLayerIndex hcS s l)).2).symm r₁)
        (fun s l => ((cols.get (bridgeStageLayerIndex hcS s l)).2).symm r₁)
        (fun s l => ((cols.get (bridgeStageLayerIndex hcS s l)).2).symm r₂)
        (fun s l => ((cols.get (bridgeStageLayerIndex hcS s l)).2).symm r₂)
      have hw' := abs_le.mp hw
      dsimp only
      rw [hM₁, hM₂, abs_le]
      exact ⟨by linarith [hrt1_lo, hrt2_hi, hw'.1], by linarith [hrt1_hi, hrt2_lo, hw'.2]⟩
    hcol_ideal_width := fun c₁ c₂ => by
      obtain ⟨ct₁, hct1_lo, hct1_hi, hM₁⟩ := hcol_decomp c₁
      obtain ⟨ct₂, hct2_lo, hct2_hi, hM₂⟩ := hcol_decomp c₂
      have hw := roles.hord_stage_width
        (fun s l => ((rows.get (bridgeStageLayerIndex hrS s l)).2).symm c₁)
        (fun s l => ((rows.get (bridgeStageLayerIndex hrS s l)).2).symm c₁)
        (fun s l => ((rows.get (bridgeStageLayerIndex hrS s l)).2).symm c₂)
        (fun s l => ((rows.get (bridgeStageLayerIndex hrS s l)).2).symm c₂)
        (fun _ _ => c₁) (fun _ l => (p l).symm c₁)
        (fun _ _ => c₂) (fun _ l => (p l).symm c₂)
      have hw' := abs_le.mp hw
      dsimp only
      rw [hM₁, hM₂, abs_le]
      exact ⟨by linarith [hct1_lo, hct2_hi, hw'.1], by linarith [hct1_hi, hct2_lo, hw'.2]⟩
  }⟩

end

end Sude
