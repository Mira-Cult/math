import Sude.FWBridgeControllerSlots

/-! Place FW bridge diagonal blocks in supplied RP1 rectangles. -/
namespace Sude
noncomputable section

/-- Install the 24 diagonal double blocks from each FW bridge stage in
the first 120 rectangles of a supplied RP1 packing. The existing choice
assigns the first 12 blocks of each stage to the main diagonal and the
next 12 to the antidiagonal. The selected rectangles must avoid the prior
reserved cells; ordinary networks and a joint controller layout are not
constructed here. -/
theorem fw_install_bridge_diagonal_rectangles
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (n L : ℕ) (initial : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (otherChoice : Fin L → Bool) (a : Cell n ≃ Fin (n * n))
    (reservedCells : Finset (Cell n))
    (hreserved : ∀ c ∈ reservedCells, entry a c ∈ initial)
    (hfree : ∀ t : Fin (5 * (4 * 6)), Disjoint
      (rectangleCells (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.firstColumn hs (bridgeDiagonalChoice hrect otherChoice)
          (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.secondColumn hs (bridgeDiagonalChoice hrect otherChoice)
          (bridgeDiagonalRectangle hrect t))) reservedCells) :
    ∃ a' : Cell n ≃ Fin (n * n),
      (∀ t side, entry a' (packedRectangleCorner hs (bridgeDiagonalChoice hrect otherChoice)
          (bridgeDiagonalRectangle hrect t, side)) =
        fwBridgeStageEndpoint n initial batches hvalid (fwBridgeDiagonalSlot n (t, side))) ∧
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
              (bridgeDiagonalRectangle hrect t)) + gap) := by
  let choice := bridgeDiagonalChoice hrect otherChoice
  let rectangle := bridgeDiagonalRectangle hrect
  let cells : Fin (5 * (4 * 6)) × Fin 4 → Cell n := fun x =>
    packedRectangleCorner hs choice (rectangle x.1, x.2)
  let slots := fwBridgeDiagonalSlot n
  have hcells : Function.Injective cells := by
    rintro ⟨d, s⟩ ⟨e, t⟩ heq
    have heq' := packedRectangleCorner_injective hs choice heq
    have hde : d = e := bridgeDiagonalRectangle_injective hrect (congrArg Prod.fst heq')
    subst e
    have hst : s = t := congrArg Prod.snd heq'
    cases hst
    rfl
  let values : (Fin (5 * (4 * 6)) × Fin 4) → pool n := fun x =>
    ⟨fwBridgeStageEndpoint n initial batches hvalid (slots x),
      (fwBridgeStageEndpoint_pool_avoids bmor upper n initial batches hvalid hn hnmax (slots x)).1⟩
  have hvalues : Function.Injective values := by
    intro x y heq
    apply fwBridgeDiagonalSlot_injective n
    apply fwBridgeStageEndpoint_injective n initial batches hvalid
    exact congrArg Subtype.val heq
  have hnew : ∀ x, cells x ∉ reservedCells := by
    rintro ⟨t, side⟩ hc
    exact Finset.disjoint_left.mp (hfree t) (packedRectangleCorner_mem hs choice (rectangle t) side) hc
  have hav : ∀ x c, c ∈ reservedCells → (values x).val ≠ entry a c := by
    intro x c hc heq
    have hnot := (fwBridgeStageEndpoint_pool_avoids bmor upper n initial batches hvalid hn hnmax (slots x)).2
    apply hnot
    change (values x).val ∈ initial
    rw [heq]
    exact hreserved c hc
  obtain ⟨a', hplace, hfixed⟩ :=
    place_distinct_pool_entries_preserving a cells values reservedCells hcells hvalues hnew hav
  refine ⟨a', ?_, hfixed, ?_⟩
  · intro t side
    exact hplace (t, side)
  · intro t
    let j := (slots (t, 0)).1.1
    let i := (slots (t, 0)).1.2
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
    · have ha := hplace (t, 1)
      have hb := hplace (t, 0)
      change entry a' (RectanglePacking.firstRow hs (rectangle t),
          RectanglePacking.secondColumn hs choice (rectangle t)) = _ at ha
      change entry a' (RectanglePacking.firstRow hs (rectangle t),
          RectanglePacking.firstColumn hs choice (rectangle t)) = _ at hb
      rw [ha, hb, hgap]
      change b.high₁ = b.low₁ + (b.high₁ - b.low₁)
      dsimp only [b] at *
      omega
    · have ha := hplace (t, 2)
      have hb := hplace (t, 3)
      change entry a' (RectanglePacking.secondRow hs (rectangle t),
          RectanglePacking.firstColumn hs choice (rectangle t)) = _ at ha
      change entry a' (RectanglePacking.secondRow hs (rectangle t),
          RectanglePacking.secondColumn hs choice (rectangle t)) = _ at hb
      rw [ha, hb, hgap]
      change b.high₂ = b.low₂ + (b.high₁ - b.low₁)
      dsimp only [b] at *
      omega

end
end Sude
