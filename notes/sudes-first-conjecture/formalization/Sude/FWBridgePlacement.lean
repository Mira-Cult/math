import Sude.FWBridgeEndpoints

/-! Placement of actual FW endpoints into supplied cells, without geometry. -/
namespace Sude
noncomputable section

/-- Place the actual FW bridge endpoints in any supplied injective cells,
while fixing cells whose current values are in the initial reservation.
Both installed pairs have the exact positive even gap used by the FW grid
theorem. This asserts no row, column, rectangle, or diagonal geometry. -/
theorem fw_install_bridge_stage_endpoints
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (n : ℕ) (initial : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (a : Cell n ≃ Fin (n * n))
    (cells : (Fin 5 × Fin (3 * (n + 8))) × Fin 4 → Cell n)
    (reservedCells : Finset (Cell n)) (hcells : Function.Injective cells)
    (hnew : ∀ x, cells x ∉ reservedCells)
    (hreserved : ∀ c ∈ reservedCells, entry a c ∈ initial) :
    ∃ a' : Cell n ≃ Fin (n * n),
      (∀ x, entry a' (cells x) = fwBridgeStageEndpoint n initial batches hvalid x) ∧
      (∀ c ∈ reservedCells, entry a' c = entry a c) ∧
      (∀ (j : Fin 5) (i : Fin (3 * (n + 8))),
        0 < selectedBridgeGap batches i j ∧ 2 ∣ selectedBridgeGap batches i j ∧
        entry a' (cells ((j, i), 1)) = entry a' (cells ((j, i), 0)) +
          selectedBridgeGap batches i j ∧
        entry a' (cells ((j, i), 2)) = entry a' (cells ((j, i), 3)) +
          selectedBridgeGap batches i j) := by
  let values : ((Fin 5 × Fin (3 * (n + 8))) × Fin 4) → pool n := fun x =>
    ⟨fwBridgeStageEndpoint n initial batches hvalid x,
      (fwBridgeStageEndpoint_pool_avoids bmor upper n initial batches hvalid hn hnmax x).1⟩
  have hinj : Function.Injective values := by
    intro x y h
    apply fwBridgeStageEndpoint_injective n initial batches hvalid
    exact congrArg Subtype.val h
  have hav : ∀ x c, c ∈ reservedCells → (values x).val ≠ entry a c := by
    intro x c hc heq
    have hnot := (fwBridgeStageEndpoint_pool_avoids bmor upper n initial batches hvalid hn hnmax x).2
    apply hnot
    change (values x).val ∈ initial
    rw [heq]
    exact hreserved c hc
  obtain ⟨a', hplace, hfixed⟩ :=
    place_distinct_pool_entries_preserving a cells values reservedCells hcells hinj hnew hav
  refine ⟨a', hplace, hfixed, ?_⟩
  intro j i
  let b := fwBridgeStageBlock n initial batches hvalid j i
  have hv := fwBridgeStageBlock_valid n initial batches hvalid j i
  have hg := (hvalid j j.isLt).1.2.2.2.2 b
    (fwBridgeStageBlock_mem n initial batches hvalid j i)
  have hgap := fwBridgeStageBlock_gap n initial batches hvalid j i
  rcases hv with ⟨_, _, _, _, _, _, hfirst, hsecond, heq⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hgap]
    exact hg.1
  · rw [hgap]
    exact hg.2.1
  · rw [hplace, hplace, hgap]
    change b.high₁ = b.low₁ + (b.high₁ - b.low₁)
    dsimp only [b] at *
    omega
  · rw [hplace, hplace, hgap]
    change b.high₂ = b.low₂ + (b.high₁ - b.low₁)
    dsimp only [b] at *
    omega

/-- The FW range has enough total cells for all five bridge batches. This
cardinality result supplies no line or rectangle placement constraints. -/
theorem fw_bridge_cells_of_capacity {n : ℕ} (hn : 19485 ≤ n) :
    ∃ cells : (Fin 5 × Fin (3 * (n + 8))) × Fin 4 → Cell n,
      Function.Injective cells := by
  have hmul : 19485 * n ≤ n * n := Nat.mul_le_mul_right n hn
  have hcapacity : 5 * (3 * (n + 8)) * 4 + (∅ : Finset (Cell n)).card ≤ n * n := by
    simp only [Finset.card_empty, Nat.add_zero]
    nlinarith
  obtain ⟨cells, hinj, _⟩ := bridge_stage_cells_of_capacity 5 (3 * (n + 8)) ∅ hcapacity
  exact ⟨cells, hinj⟩

/-- With an empty initial reservation, total FW cell capacity supplies an
arbitrary placement for the five selected batches in an exact-pool square.
These cells are not asserted to form the FW physical controller layout. -/
theorem fw_install_bridge_stage_endpoints_of_capacity
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (a : Cell n ≃ Fin (n * n)) :
    ∃ (cells : (Fin 5 × Fin (3 * (n + 8))) × Fin 4 → Cell n)
      (a' : Cell n ≃ Fin (n * n)),
      Function.Injective cells ∧
      (∀ x, entry a' (cells x) = fwBridgeStageEndpoint n ∅ batches hvalid x) ∧
      (∀ (j : Fin 5) (i : Fin (3 * (n + 8))),
        0 < selectedBridgeGap batches i j ∧ 2 ∣ selectedBridgeGap batches i j ∧
        entry a' (cells ((j, i), 1)) = entry a' (cells ((j, i), 0)) +
          selectedBridgeGap batches i j ∧
        entry a' (cells ((j, i), 2)) = entry a' (cells ((j, i), 3)) +
          selectedBridgeGap batches i j) := by
  obtain ⟨cells, hcells⟩ := fw_bridge_cells_of_capacity hnlo
  obtain ⟨a', hplace, _, hgap⟩ := fw_install_bridge_stage_endpoints bmor upper n ∅ batches
    hvalid (by omega) (by omega) a cells ∅ hcells (by simp) (by simp)
  exact ⟨cells, a', hcells, hplace, hgap⟩

end
end Sude
