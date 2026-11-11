import Sude.FWBridgeOrdinaryPlacement

/-! Compose FW diagonal and ordinary placement on one pool permutation. -/
namespace Sude
noncomputable section

/-- Install the selected FW bridge diagonal blocks and ordinary pairs in
one square using the supplied compatible geometry. The rectangle supports
and ordinary cells must avoid the stated reservations and each other.
The result does not construct a joint physical layout or prove a controller. -/
theorem fw_install_bridge_diagonals_and_ordinary
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (n L : ℕ) (initial : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (otherChoice : Fin L → Bool) (a : Cell n ≃ Fin (n * n))
    (reservedCells : Finset (Cell n))
    (hreserved : ∀ c ∈ reservedCells, entry a c ∈ initial)
    (hrectFree : ∀ t : Fin (5 * (4 * 6)), Disjoint
      (rectangleCells (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.firstColumn hs (bridgeDiagonalChoice hrect otherChoice)
          (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.secondColumn hs (bridgeDiagonalChoice hrect otherChoice)
          (bridgeDiagonalRectangle hrect t))) reservedCells)
    (cells : (Fin 5 × (Fin 3 × Fin n)) × (Bool × Bool) → Cell n)
    (hcells : Function.Injective cells)
    (hfree : ∀ x, cells x ∉ reservedCells ∧ ∀ t side,
      cells x ≠ packedRectangleCorner hs (bridgeDiagonalChoice hrect otherChoice)
        (bridgeDiagonalRectangle hrect t, side)) :
    ∃ a' : Cell n ≃ Fin (n * n),
      (∀ t side, entry a' (packedRectangleCorner hs (bridgeDiagonalChoice hrect otherChoice)
          (bridgeDiagonalRectangle hrect t, side)) =
        fwBridgeStageEndpoint n initial batches hvalid (fwBridgeDiagonalSlot n (t, side))) ∧
      (∀ x, entry a' (cells x) =
        fwBridgeStageEndpoint n initial batches hvalid (fwBridgeOrdinarySlot n x)) ∧
      (∀ c ∈ reservedCells, entry a' c = entry a c) ∧
      (∀ t : Fin (5 * (4 * 6)),
        let block := (fwBridgeDiagonalSlot n (t, 0)).1
        let gap := selectedBridgeGap batches block.2 block.1
        0 < gap ∧ 2 ∣ gap ∧
        entry a' (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t),
            RectanglePacking.secondColumn hs (bridgeDiagonalChoice hrect otherChoice)
              (bridgeDiagonalRectangle hrect t)) =
          entry a' (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t),
            RectanglePacking.firstColumn hs (bridgeDiagonalChoice hrect otherChoice)
              (bridgeDiagonalRectangle hrect t)) + gap ∧
        entry a' (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t),
            RectanglePacking.firstColumn hs (bridgeDiagonalChoice hrect otherChoice)
              (bridgeDiagonalRectangle hrect t)) =
          entry a' (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t),
            RectanglePacking.secondColumn hs (bridgeDiagonalChoice hrect otherChoice)
              (bridgeDiagonalRectangle hrect t)) + gap) ∧
      (∀ (j : Fin 5) (p : Fin 3 × Fin n) (network : Bool),
        let block := (fwBridgeOrdinarySlot n ((j, p), (network, false))).1.2
        let gap := selectedBridgeGap batches block j
        0 < gap ∧ 2 ∣ gap ∧
        entry a' (cells ((j, p), (network, true))) =
          entry a' (cells ((j, p), (network, false))) + gap) := by
  obtain ⟨a₁, hdiag, hfixed₁, hdiagGap⟩ :=
    fw_install_bridge_diagonal_rectangles bmor upper n L initial batches hvalid hn hnmax
      hrect hs otherChoice a reservedCells hreserved hrectFree
  have hreserved₁ : ∀ c ∈ reservedCells, entry a₁ c ∈ initial := by
    intro c hc
    rw [hfixed₁ c hc]
    exact hreserved c hc
  obtain ⟨a', hord, hfixed₂, hdiagFixed, hordGap⟩ :=
    fw_install_ordinary_bridge_slots_preserving_rectangles bmor upper n L initial batches
      hvalid hn hnmax hrect hs otherChoice a₁ hdiag reservedCells hreserved₁ cells hcells hfree
  refine ⟨a', ?_, hord, ?_, ?_, hordGap⟩
  · intro t side
    exact (hdiagFixed t side).trans (hdiag t side)
  · intro c hc
    exact (hfixed₂ c hc).trans (hfixed₁ c hc)
  · intro t
    obtain ⟨hpos, heven, htop, hbot⟩ := hdiagGap t
    have h₀ := hdiagFixed t 0
    have h₁ := hdiagFixed t 1
    have h₂ := hdiagFixed t 2
    have h₃ := hdiagFixed t 3
    change entry a' (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t),
        RectanglePacking.firstColumn hs (bridgeDiagonalChoice hrect otherChoice)
          (bridgeDiagonalRectangle hrect t)) = _ at h₀
    change entry a' (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t),
        RectanglePacking.secondColumn hs (bridgeDiagonalChoice hrect otherChoice)
          (bridgeDiagonalRectangle hrect t)) = _ at h₁
    change entry a' (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t),
        RectanglePacking.firstColumn hs (bridgeDiagonalChoice hrect otherChoice)
          (bridgeDiagonalRectangle hrect t)) = _ at h₂
    change entry a' (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t),
        RectanglePacking.secondColumn hs (bridgeDiagonalChoice hrect otherChoice)
          (bridgeDiagonalRectangle hrect t)) = _ at h₃
    refine ⟨hpos, heven, ?_, ?_⟩
    · rw [h₁, h₀]
      exact htop
    · rw [h₂, h₃]
      exact hbot

end
end Sude
