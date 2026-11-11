import Sude.FWBridgeRectangles

/-! Install supplied ordinary FW slots while fixing the diagonal rectangles. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- The ordinary slot's two endpoints use the same positive even gap as
their selected FW double block, for either ordinary network. -/
theorem fw_bridge_ordinary_endpoint_gap (n : ℕ) (initial : Finset ℕ)
    (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (j : Fin 5) (p : Fin 3 × Fin n) (network : Bool) :
    let block := (fwBridgeOrdinarySlot n ((j, p), (network, false))).1.2
    let gap := selectedBridgeGap batches block j
    0 < gap ∧ 2 ∣ gap ∧
      fwBridgeStageEndpoint n initial batches hvalid
          (fwBridgeOrdinarySlot n ((j, p), (network, true))) =
        fwBridgeStageEndpoint n initial batches hvalid
          (fwBridgeOrdinarySlot n ((j, p), (network, false))) + gap := by
  let i := bridgeOrdinaryBlockIndex (r := 3) (d := 6)
    (k := 3 * (n + 8)) (by omega) p
  let b := fwBridgeStageBlock n initial batches hvalid j i
  have hv := fwBridgeStageBlock_valid n initial batches hvalid j i
  have hg := (hvalid j j.isLt).1.2.2.2.2 b
    (fwBridgeStageBlock_mem n initial batches hvalid j i)
  have hgap := fwBridgeStageBlock_gap n initial batches hvalid j i
  rcases hv with ⟨_, _, _, _, _, _, hfirst, hsecond, heq⟩
  cases network
  · change 0 < selectedBridgeGap batches i j ∧ 2 ∣ selectedBridgeGap batches i j ∧
      b.high₁ = b.low₁ + selectedBridgeGap batches i j
    rw [hgap]
    dsimp only [b] at *
    exact ⟨hg.1, hg.2.1, by omega⟩
  · change 0 < selectedBridgeGap batches i j ∧ 2 ∣ selectedBridgeGap batches i j ∧
      b.high₂ = b.low₂ + selectedBridgeGap batches i j
    rw [hgap]
    dsimp only [b] at *
    exact ⟨hg.1, hg.2.1, by omega⟩

/-- Place all ordinary FW bridge endpoints in supplied injective cells.
The stated diagonal rectangles are already installed, and all their cells
and earlier reserved cells are fixed. Disjointness from those cells and the
reserved-value correspondence are hypotheses; this does not construct
row/column network geometry or a joint controller layout. -/
theorem fw_install_ordinary_bridge_slots_preserving_rectangles
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (n L : ℕ) (initial : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (otherChoice : Fin L → Bool) (a : Cell n ≃ Fin (n * n))
    (hdiag : ∀ t side, entry a (packedRectangleCorner hs (bridgeDiagonalChoice hrect otherChoice)
        (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeDiagonalSlot n (t, side)))
    (reservedCells : Finset (Cell n))
    (hreserved : ∀ c ∈ reservedCells, entry a c ∈ initial)
    (cells : (Fin 5 × (Fin 3 × Fin n)) × (Bool × Bool) → Cell n)
    (hcells : Function.Injective cells)
    (hfree : ∀ x, cells x ∉ reservedCells ∧ ∀ t side,
      cells x ≠ packedRectangleCorner hs (bridgeDiagonalChoice hrect otherChoice)
        (bridgeDiagonalRectangle hrect t, side)) :
    ∃ a' : Cell n ≃ Fin (n * n),
      (∀ x, entry a' (cells x) =
        fwBridgeStageEndpoint n initial batches hvalid (fwBridgeOrdinarySlot n x)) ∧
      (∀ c ∈ reservedCells, entry a' c = entry a c) ∧
      (∀ t side, entry a' (packedRectangleCorner hs (bridgeDiagonalChoice hrect otherChoice)
          (bridgeDiagonalRectangle hrect t, side)) =
        entry a (packedRectangleCorner hs (bridgeDiagonalChoice hrect otherChoice)
          (bridgeDiagonalRectangle hrect t, side))) ∧
      (∀ (j : Fin 5) (p : Fin 3 × Fin n) (network : Bool),
        let block := (fwBridgeOrdinarySlot n ((j, p), (network, false))).1.2
        let gap := selectedBridgeGap batches block j
        0 < gap ∧ 2 ∣ gap ∧
        entry a' (cells ((j, p), (network, true))) =
          entry a' (cells ((j, p), (network, false))) + gap) := by
  classical
  let diag : Fin (5 * (4 * 6)) × Fin 4 → Cell n := fun x =>
    packedRectangleCorner hs (bridgeDiagonalChoice hrect otherChoice)
      (bridgeDiagonalRectangle hrect x.1, x.2)
  let protectedCells := reservedCells ∪ Finset.univ.image diag
  let values : ((Fin 5 × (Fin 3 × Fin n)) × (Bool × Bool)) → pool n := fun x =>
    ⟨fwBridgeStageEndpoint n initial batches hvalid (fwBridgeOrdinarySlot n x),
      (fwBridgeStageEndpoint_pool_avoids bmor upper n initial batches hvalid hn hnmax
        (fwBridgeOrdinarySlot n x)).1⟩
  have hvalues : Function.Injective values := by
    intro x y heq
    apply fwBridgeOrdinarySlot_injective n
    apply fwBridgeStageEndpoint_injective n initial batches hvalid
    exact congrArg Subtype.val heq
  have hnew : ∀ x, cells x ∉ protectedCells := by
    intro x hx
    rcases Finset.mem_union.mp hx with hr | hd
    · exact (hfree x).1 hr
    · obtain ⟨⟨t, side⟩, _, heq⟩ := Finset.mem_image.mp hd
      exact (hfree x).2 t side heq.symm
  have hav : ∀ x c, c ∈ protectedCells → (values x).val ≠ entry a c := by
    intro x c hc heq
    rcases Finset.mem_union.mp hc with hr | hd
    · have hnot := (fwBridgeStageEndpoint_pool_avoids bmor upper n initial batches hvalid
        hn hnmax (fwBridgeOrdinarySlot n x)).2
      apply hnot
      change (values x).val ∈ initial
      rw [heq]
      exact hreserved c hr
    · obtain ⟨⟨t, side⟩, _, rfl⟩ := Finset.mem_image.mp hd
      have hdiag' := hdiag t side
      have he : fwBridgeStageEndpoint n initial batches hvalid (fwBridgeOrdinarySlot n x) =
          fwBridgeStageEndpoint n initial batches hvalid (fwBridgeDiagonalSlot n (t, side)) := by
        exact heq.trans hdiag'
      have hslots := (fwBridgeStageEndpoint_injective n initial batches hvalid) he
      have himpossible :
          (Sum.inr x : (Fin (5 * (4 * 6)) × Fin 4) ⊕
            ((Fin 5 × (Fin 3 × Fin n)) × (Bool × Bool))) = Sum.inl (t, side) := by
        apply (fwBridgeControllerSlot_bijective n).1
        exact hslots
      cases himpossible
  obtain ⟨a', hplace, hfixed⟩ :=
    place_distinct_pool_entries_preserving a cells values protectedCells hcells hvalues hnew hav
  refine ⟨a', hplace, ?_, ?_, ?_⟩
  · intro c hc
    exact hfixed c (Finset.mem_union_left _ hc)
  · intro t side
    exact hfixed (diag (t, side)) (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(t, side), Finset.mem_univ _, rfl⟩))
  · intro j p network
    have hgap := fw_bridge_ordinary_endpoint_gap n initial batches hvalid j p network
    refine ⟨hgap.1, hgap.2.1, ?_⟩
    rw [hplace, hplace]
    exact hgap.2.2

end
end Sude
