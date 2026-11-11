import Sude.BridgeChosenGrid
import Sude.DoublePairPlacement

/-! Physical installation of the actual batches selected by bridge stages. -/
namespace Sude
noncomputable section

/-- Every endpoint of a selected block occurs in its batch's side sets. -/
theorem doublePair_footprint_subset_batch (blocks : List DoublePair) (b : DoublePair)
    (hb : b ∈ blocks) : b.footprint ⊆ doubleBatchLow blocks ∪ doubleBatchHigh blocks := by
  intro x hx
  simp only [DoublePair.footprint, Finset.mem_insert, Finset.mem_singleton] at hx
  have hb' : b ∈ blocks.toFinset := List.mem_toFinset.mpr hb
  rcases hx with rfl | rfl | rfl | rfl
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨b, hb', by simp⟩)
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨b, hb', by simp⟩)
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b, hb', by simp⟩)
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b, hb', by simp⟩)

/-- Every lower bridge stock entry is strictly below every upper entry of
the same stage. -/
theorem bridge_stocks_order (X R : ℝ) (hX : 0 < X) (hR : 0 < R) :
    ∀ a ∈ bridgeLowStock X R, ∀ b ∈ bridgeHighStock X R, a < b := by
  intro a ha b hb
  have hg := bridge_window_geometry X R hX hR
  have ha' := (mem_apInterval_iff (bridgeLowStart X R) (bridgeLowEnd X R) 2 1
    (by linarith [hg.2.2.1]) (by linarith [hg.2.2.1, hg.2.2.2.1]) a).mp ha
  have hb' := (mem_apInterval_iff (bridgeHighStart X R) (bridgeHighEnd X R) 2 1
    (by linarith [hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1])
    (by linarith [hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1]) b).mp hb
  exact (bridge_cross_gap X R hX hR a b ⟨ha'.2.1, ha'.2.2.1⟩
    ⟨hb'.2.1, hb'.2.2.1⟩).1

/-- The chosen block at a stage and within-stage index. -/
def bridgeStageBlock (n : ℕ) (initial : Finset ℕ) (radii : ℕ → ℝ)
    (batches : ℕ → List DoublePair) (k J : ℕ)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (j : Fin J) (i : Fin k) : DoublePair :=
  (batches j).get ⟨i, by rw [(hvalid j j.isLt).1]; exact i.isLt⟩

theorem bridgeStageBlock_mem (n : ℕ) (initial : Finset ℕ) (radii : ℕ → ℝ)
    (batches : ℕ → List DoublePair) (k J : ℕ)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (j : Fin J) (i : Fin k) : bridgeStageBlock n initial radii batches k J hvalid j i ∈ batches j := by
  apply List.get_mem

theorem bridgeStageBlock_valid (n : ℕ) (initial : Finset ℕ) (radii : ℕ → ℝ)
    (batches : ℕ → List DoublePair) (k J : ℕ)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (j : Fin J) (i : Fin k) :
    (bridgeStageBlock n initial radii batches k J hvalid j i).valid
      (bridgeLowStock (poolMaximum n) (radii j) \
        priorBridgeReservation initial (Finset.range j) batches)
      (bridgeHighStock (poolMaximum n) (radii j) \
        priorBridgeReservation initial (Finset.range j) batches) :=
  (hvalid j j.isLt).2.1 _ (bridgeStageBlock_mem n initial radii batches k J hvalid j i)

/-- Different selected blocks in one stage have disjoint endpoint sets. -/
theorem bridgeStageBlock_same_stage_disjoint (n : ℕ) (initial : Finset ℕ) (radii : ℕ → ℝ)
    (batches : ℕ → List DoublePair) (k J : ℕ)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (j : Fin J) (i i' : Fin k) (hne : i ≠ i') :
    Disjoint (bridgeStageBlock n initial radii batches k J hvalid j i).footprint
      (bridgeStageBlock n initial radii batches k J hvalid j i').footprint := by
  let p : Fin (batches j).length := ⟨i, by rw [(hvalid j j.isLt).1]; exact i.isLt⟩
  let q : Fin (batches j).length := ⟨i', by rw [(hvalid j j.isLt).1]; exact i'.isLt⟩
  have hpair := (hvalid j j.isLt).2.2.1
  have hpq : p ≠ q := by
    intro heq
    apply hne
    apply Fin.ext
    exact congrArg (fun z : Fin (batches j).length => z.val) heq
  change Disjoint ((batches j).get p).footprint ((batches j).get q).footprint
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · exact hpair.rel_get_of_lt hlt
  · exact (hpair.rel_get_of_lt hgt).symm

/-- Different bridge stages use disjoint actual entries, not merely disjoint
abstract coordinates. -/
theorem bridgeStageBlock_different_stage_disjoint (n : ℕ) (initial : Finset ℕ)
    (radii : ℕ → ℝ) (batches : ℕ → List DoublePair) (k J : ℕ)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (j j' : Fin J) (i i' : Fin k) (hne : j ≠ j') :
    Disjoint (bridgeStageBlock n initial radii batches k J hvalid j i).footprint
      (bridgeStageBlock n initial radii batches k J hvalid j' i').footprint := by
  have hd := bridgeStageSequence_disjoint n initial radii batches k J hvalid
    j j.isLt j' j'.isLt (by intro h; apply hne; exact Fin.ext h)
  exact hd.mono
    (doublePair_footprint_subset_batch (batches j) _
      (bridgeStageBlock_mem n initial radii batches k J hvalid j i))
    (doublePair_footprint_subset_batch (batches j') _
      (bridgeStageBlock_mem n initial radii batches k J hvalid j' i'))

def bridgeStageEndpoint (n : ℕ) (initial : Finset ℕ) (radii : ℕ → ℝ)
    (batches : ℕ → List DoublePair) (k J : ℕ)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (x : (Fin J × Fin k) × Fin 4) : ℕ :=
  (bridgeStageBlock n initial radii batches k J hvalid x.1.1 x.1.2).endpoint x.2

/-- Each physical stage/block/side slot addresses a different original
entry, including slots belonging to distinct overlapping windows. -/
theorem bridgeStageEndpoint_injective (n : ℕ) (initial : Finset ℕ) (radii : ℕ → ℝ)
    (batches : ℕ → List DoublePair) (k J : ℕ)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hpositive : ∀ j < J, 0 < radii j) :
    Function.Injective (bridgeStageEndpoint n initial radii batches k J hvalid) := by
  rintro ⟨⟨j, i⟩, side⟩ ⟨⟨j', i'⟩, side'⟩ heq
  change (bridgeStageBlock n initial radii batches k J hvalid j i).endpoint side =
    (bridgeStageBlock n initial radii batches k J hvalid j' i').endpoint side' at heq
  by_cases hj : j = j'
  · subst j'
    by_cases hi : i = i'
    · subst i'
      have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
      have horder := bridge_stocks_order (poolMaximum n) (radii j) hX (hpositive j j.isLt)
      have hv := bridgeStageBlock_valid n initial radii batches k J hvalid j i
      have hv' := DoublePair.valid_mono hv Finset.sdiff_subset Finset.sdiff_subset
      have hs : side = side' := DoublePair.endpoint_injective _ _ _ horder hv' heq
      cases hs
      rfl
    · have hd := bridgeStageBlock_same_stage_disjoint n initial radii batches k J hvalid j i i' hi
      have hleft := DoublePair.endpoint_mem (bridgeStageBlock n initial radii batches k J hvalid j i) side
      have hright := DoublePair.endpoint_mem (bridgeStageBlock n initial radii batches k J hvalid j i') side'
      rw [← heq] at hright
      exact False.elim (Finset.disjoint_left.mp hd hleft hright)
  · have hd := bridgeStageBlock_different_stage_disjoint n initial radii batches k J hvalid j j' i i' hj
    have hleft := DoublePair.endpoint_mem (bridgeStageBlock n initial radii batches k J hvalid j i) side
    have hright := DoublePair.endpoint_mem (bridgeStageBlock n initial radii batches k J hvalid j' i') side'
    rw [← heq] at hright
    exact False.elim (Finset.disjoint_left.mp hd hleft hright)

/-- Every indexed endpoint is an actual pool prime and avoids the initial
reservation. Both facts follow from the previously proved stage invariant. -/
theorem bridgeStageEndpoint_pool_avoids (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (n : ℕ) (initial : Finset ℕ) (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (k J : ℕ) (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18) (hpositive : ∀ j < J, 0 < radii j)
    (x : (Fin J × Fin k) × Fin 4) :
    bridgeStageEndpoint n initial radii batches k J hvalid x ∈ pool n ∧
      bridgeStageEndpoint n initial radii batches k J hvalid x ∉ initial := by
  rcases x with ⟨⟨j, i⟩, side⟩
  let b := bridgeStageBlock n initial radii batches k J hvalid j i
  have hv := bridgeStageBlock_valid n initial radii batches k J hvalid j i
  have hstock := bmor_bridge_stocks bmor upper n (radii j) hn hnmax (hpositive j j.isLt)
  have hinit : initial ⊆ priorBridgeReservation initial (Finset.range j) batches := by
    intro x hx
    exact Finset.mem_union_left _ hx
  have hmem := DoublePair.endpoint_mem b side
  simp only [DoublePair.footprint, Finset.mem_insert, Finset.mem_singleton] at hmem
  change b.endpoint side ∈ pool n ∧ b.endpoint side ∉ initial
  rcases hmem with heq | heq | heq | heq
  · rw [heq]
    exact ⟨hstock.2.2.1 _ (Finset.mem_sdiff.mp hv.1).1,
      fun h => (Finset.mem_sdiff.mp hv.1).2 (hinit h)⟩
  · rw [heq]
    exact ⟨hstock.2.2.1 _ (Finset.mem_sdiff.mp hv.2.1).1,
      fun h => (Finset.mem_sdiff.mp hv.2.1).2 (hinit h)⟩
  · rw [heq]
    exact ⟨hstock.2.2.2 _ (Finset.mem_sdiff.mp hv.2.2.1).1,
      fun h => (Finset.mem_sdiff.mp hv.2.2.1).2 (hinit h)⟩
  · rw [heq]
    exact ⟨hstock.2.2.2 _ (Finset.mem_sdiff.mp hv.2.2.2.1).1,
      fun h => (Finset.mem_sdiff.mp hv.2.2.2.1).2 (hinit h)⟩

/-- The stage-indexed block and the gap used in the grid theorem agree. -/
theorem bridgeStageBlock_gap (n : ℕ) (initial : Finset ℕ) (radii : ℕ → ℝ)
    (batches : ℕ → List DoublePair) (k J : ℕ)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (j : Fin J) (i : Fin k) :
    selectedBridgeGap batches i j =
      (bridgeStageBlock n initial radii batches k J hvalid j i).high₁ -
        (bridgeStageBlock n initial radii batches k J hvalid j i).low₁ := by
  have hi : i.val < (batches j).length := by rw [(hvalid j j.isLt).1]; exact i.isLt
  simp [selectedBridgeGap, List.getElem?_eq_getElem hi, bridgeStageBlock]

/-- Install the entire selected bridge history simultaneously into the
provided distinct cells. Initial reserved cells are retained, and both
equal-gap equations use exactly the gap already used by the grid proof. -/
theorem install_bridge_stage_blocks (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (n : ℕ) (initial : Finset ℕ) (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (k J : ℕ) (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18) (hpositive : ∀ j < J, 0 < radii j)
    (a : Cell n ≃ Fin (n * n)) (cells : (Fin J × Fin k) × Fin 4 → Cell n)
    (reservedCells : Finset (Cell n)) (hcells : Function.Injective cells)
    (hnew : ∀ x, cells x ∉ reservedCells)
    (hreserved : ∀ c ∈ reservedCells, entry a c ∈ initial) :
    ∃ a' : Cell n ≃ Fin (n * n),
      (∀ x, entry a' (cells x) = bridgeStageEndpoint n initial radii batches k J hvalid x) ∧
      (∀ c ∈ reservedCells, entry a' c = entry a c) ∧
      (∀ j : Fin J, ∀ i : Fin k, 0 < selectedBridgeGap batches i j ∧
        entry a' (cells ((j, i), 1)) = entry a' (cells ((j, i), 0)) +
          selectedBridgeGap batches i j ∧
        entry a' (cells ((j, i), 2)) = entry a' (cells ((j, i), 3)) +
          selectedBridgeGap batches i j) := by
  let values : ((Fin J × Fin k) × Fin 4) → pool n := fun x =>
    ⟨bridgeStageEndpoint n initial radii batches k J hvalid x,
      (bridgeStageEndpoint_pool_avoids bmor upper n initial radii batches k J hvalid
        hn hnmax hpositive x).1⟩
  have hinj : Function.Injective values := by
    intro x y heq
    apply bridgeStageEndpoint_injective n initial radii batches k J hvalid hpositive
    exact congrArg Subtype.val heq
  have hav : ∀ x c, c ∈ reservedCells → (values x).val ≠ entry a c := by
    intro x c hc heq
    have ha := (bridgeStageEndpoint_pool_avoids bmor upper n initial radii batches k J hvalid
      hn hnmax hpositive x).2
    apply ha
    change (values x).val ∈ initial
    rw [heq]
    exact hreserved c hc
  obtain ⟨a', hplace, hfixed⟩ :=
    place_distinct_pool_entries_preserving a cells values reservedCells hcells hinj hnew hav
  refine ⟨a', hplace, hfixed, ?_⟩
  intro j i
  have hv := bridgeStageBlock_valid n initial radii batches k J hvalid j i
  rcases hv with ⟨_, _, _, _, _, _, hfirst, hsecond, heq⟩
  have hgap := bridgeStageBlock_gap n initial radii batches k J hvalid j i
  refine ⟨by rw [hgap]; omega, ?_, ?_⟩
  · rw [hplace, hplace, hgap]
    change (bridgeStageBlock n initial radii batches k J hvalid j i).high₁ =
      (bridgeStageBlock n initial radii batches k J hvalid j i).low₁ +
        ((bridgeStageBlock n initial radii batches k J hvalid j i).high₁ -
          (bridgeStageBlock n initial radii batches k J hvalid j i).low₁)
    omega
  · rw [hplace, hplace, hgap]
    change (bridgeStageBlock n initial radii batches k J hvalid j i).high₂ =
      (bridgeStageBlock n initial radii batches k J hvalid j i).low₂ +
        ((bridgeStageBlock n initial radii batches k J hvalid j i).high₁ -
          (bridgeStageBlock n initial radii batches k J hvalid j i).low₁)
    omega

/-- A total cell-capacity inequality supplies distinct unreserved cells for
all four endpoints of every block. It does not assert row, column, or
diagonal geometry. -/
theorem bridge_stage_cells_of_capacity {n : ℕ} (J k : ℕ) (reserved : Finset (Cell n))
    (hcapacity : J * k * 4 + reserved.card ≤ n * n) :
    ∃ cells : (Fin J × Fin k) × Fin 4 → Cell n,
      Function.Injective cells ∧ ∀ x, cells x ∉ reserved := by
  classical
  let available : Finset (Cell n) := Finset.univ \ reserved
  have hcount : available.card + reserved.card = n * n := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ reserved)
    simpa [available, Cell, Finset.card_univ, Fintype.card_prod] using h
  have hcard : Fintype.card ((Fin J × Fin k) × Fin 4) ≤ available.card := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  have hbound : Fintype.card ((Fin J × Fin k) × Fin 4) ≤
      Fintype.card {c : Cell n // c ∈ available} := by
    simpa only [Fintype.card_coe] using hcard
  let slots := Fintype.equivFin ((Fin J × Fin k) × Fin 4)
  let free := Fintype.equivFin {c : Cell n // c ∈ available}
  let pick := fun x => free.symm (Fin.castLE hbound (slots x))
  refine ⟨fun x => (pick x).val, ?_, ?_⟩
  · intro x y heq
    have hp : pick x = pick y := Subtype.ext heq
    apply slots.injective
    apply Fin.castLE_injective hbound
    exact free.symm.injective hp
  · intro x hx
    have hp := (pick x).property
    exact (Finset.mem_sdiff.mp hp).2 hx

/-- All selected bridge entries can be placed once the exact total-cell
capacity is paid. This interface leaves the line-specific geometry open. -/
theorem install_bridge_stage_blocks_of_capacity (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (n : ℕ) (initial : Finset ℕ) (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (k J : ℕ) (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18) (hpositive : ∀ j < J, 0 < radii j)
    (a : Cell n ≃ Fin (n * n)) (reservedCells : Finset (Cell n))
    (hreserved : ∀ c ∈ reservedCells, entry a c ∈ initial)
    (hcapacity : J * k * 4 + reservedCells.card ≤ n * n) :
    ∃ cells : (Fin J × Fin k) × Fin 4 → Cell n, ∃ a' : Cell n ≃ Fin (n * n),
      Function.Injective cells ∧ (∀ x, cells x ∉ reservedCells) ∧
      (∀ x, entry a' (cells x) = bridgeStageEndpoint n initial radii batches k J hvalid x) ∧
      (∀ c ∈ reservedCells, entry a' c = entry a c) ∧
      (∀ j : Fin J, ∀ i : Fin k, 0 < selectedBridgeGap batches i j ∧
        entry a' (cells ((j, i), 1)) = entry a' (cells ((j, i), 0)) +
          selectedBridgeGap batches i j ∧
        entry a' (cells ((j, i), 2)) = entry a' (cells ((j, i), 3)) +
          selectedBridgeGap batches i j) := by
  obtain ⟨cells, hcells, hnew⟩ := bridge_stage_cells_of_capacity J k reservedCells hcapacity
  obtain ⟨a', hplace, hfixed, hgap⟩ := install_bridge_stage_blocks bmor upper n initial radii
    batches k J hvalid hn hnmax hpositive a cells reservedCells hcells hnew hreserved
  exact ⟨cells, a', hcells, hnew, hplace, hfixed, hgap⟩

/-- Compose selection, actual grid growth and simultaneous physical
installation. The numerical budgets, total cell capacity, and initial grids
are explicit hypotheses; line-specific cell geometry is not asserted. -/
theorem select_grow_install_bridge_stages {α : Type*} [DecidableEq α]
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (n : ℕ) (reserved : Finset ℕ)
    (R₀ : ℝ) (M : ℕ → ℕ) (k : ℕ)
    (initial : Fin k → Finset α) (initialGap : Fin k → α → ℕ) (radius : Fin k → ℕ)
    (a : Cell n ≃ Fin (n * n)) (reservedCells : Finset (Cell n))
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18) (hR : 0 < R₀)
    (hgrid : ∀ i, CompleteEvenGrid (initial i) (initialGap i) (radius i))
    (hradius : ∀ i, 2 ∣ radius i) (hcoverage : ∀ i, R₀ ≤ (radius i : ℝ))
    (hreserved : ∀ c ∈ reservedCells, entry a c ∈ reserved)
    (hbudget : ∀ j, bridgeIteration (poolMaximum n) R₀ j < poolMaximum n →
      bridgeGeometricStageBudget n reserved (bridgeIteration (poolMaximum n) R₀) (M j) k j)
    (hcapacity : ∀ J,
      (poolMaximum n : ℝ) ≤ bridgeIteration (poolMaximum n) R₀ J →
      (∀ j < J, bridgeIteration (poolMaximum n) R₀ j < poolMaximum n) →
      J * k * 4 + reservedCells.card ≤ n * n) :
    ∃ (J : ℕ) (batches : ℕ → List DoublePair)
      (hvalid : ∀ j < J,
        bridgeStageValid n reserved (bridgeIteration (poolMaximum n) R₀) batches k j)
      (cells : (Fin J × Fin k) × Fin 4 → Cell n) (a' : Cell n ≃ Fin (n * n)),
      Function.Injective cells ∧ (∀ x, cells x ∉ reservedCells) ∧
      (∀ x, entry a' (cells x) =
        bridgeStageEndpoint n reserved (bridgeIteration (poolMaximum n) R₀) batches k J hvalid x) ∧
      (∀ c ∈ reservedCells, entry a' c = entry a c) ∧
      (∀ j : Fin J, ∀ i : Fin k, 0 < selectedBridgeGap batches i j ∧
        entry a' (cells ((j, i), 1)) = entry a' (cells ((j, i), 0)) +
          selectedBridgeGap batches i j ∧
        entry a' (cells ((j, i), 2)) = entry a' (cells ((j, i), 3)) +
          selectedBridgeGap batches i j) ∧
      (∀ i : Fin k,
        CompleteEvenGrid
          ((initial i).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
            (Finset.range J).image (Sum.inr : ℕ → Sum α ℕ))
          (joinedBridgeGap (initialGap i) batches i)
          (radius i + ∑ j ∈ Finset.range J, selectedBridgeGap batches i j) ∧
        (poolMaximum n : ℝ) ≤
          ((radius i + ∑ j ∈ Finset.range J, selectedBridgeGap batches i j : ℕ) : ℝ)) := by
  obtain ⟨J, batches, hstop, hbelow, hvalid, _⟩ :=
    select_bridge_until_covered bmor upper n reserved R₀ M k hn hnmax hR hbudget
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hpositive : ∀ j < J, 0 < bridgeIteration (poolMaximum n) R₀ j := by
    intro j _
    exact bridgeIteration_pos (poolMaximum n) R₀ hX hR j
  obtain ⟨cells, a', hcells, hnew, hplace, hfixed, hgap⟩ :=
    install_bridge_stage_blocks_of_capacity bmor upper n reserved
      (bridgeIteration (poolMaximum n) R₀) batches k J hvalid hn hnmax hpositive a reservedCells
      hreserved (hcapacity J hstop hbelow)
  refine ⟨J, batches, hvalid, cells, a', hcells, hnew, hplace, hfixed, hgap, ?_⟩
  intro i
  exact selectedBridgeBatches_grow_grid n reserved R₀ batches k J i (initial i) (initialGap i)
    (radius i) (hgrid i) (hradius i) (hcoverage i) hbelow hstop hvalid

end
end Sude
