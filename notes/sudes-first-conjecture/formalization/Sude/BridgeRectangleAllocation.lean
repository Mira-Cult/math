import Sude.PackedTradeSequence
import Mathlib.Data.Fintype.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-! The source's 2d rectangles per labelled diagonal at each bridge stage. -/
namespace Sude
noncomputable section

/-- Select the first 4d blocks of each stage, without reusing a block. -/
def bridgeDiagonalBlockSelect {J k d : ℕ} (hblocks : 4 * d ≤ k) :
    Fin (J * (4 * d)) → Fin J × Fin k := fun x =>
  let pair : Fin J × Fin (4 * d) := finProdFinEquiv.symm x
  (pair.1, Fin.castLE hblocks pair.2)

theorem bridgeDiagonalBlockSelect_injective {J k d : ℕ} (hblocks : 4 * d ≤ k) :
    Function.Injective (bridgeDiagonalBlockSelect (J := J) hblocks) := by
  intro x y hxy
  let px : Fin J × Fin (4 * d) := finProdFinEquiv.symm x
  let py : Fin J × Fin (4 * d) := finProdFinEquiv.symm y
  change (px.1, Fin.castLE hblocks px.2) = (py.1, Fin.castLE hblocks py.2) at hxy
  have hfirst : px.1 = py.1 := congrArg (fun z : Fin J × Fin k => z.1) hxy
  have hsecond : px.2 = py.2 := Fin.castLE_injective hblocks
    (congrArg (fun z : Fin J × Fin k => z.2) hxy)
  apply finProdFinEquiv.symm.injective
  exact Prod.ext hfirst hsecond

/-- Assign these bridge rectangles to the first distinct labels of a
larger joint RP1 packing; other labels remain available. -/
def bridgeDiagonalRectangle {J d L : ℕ} (hrect : J * (4 * d) ≤ L) :
    Fin (J * (4 * d)) → Fin L := Fin.castLE hrect

theorem bridgeDiagonalRectangle_injective {J d L : ℕ} (hrect : J * (4 * d) ≤ L) :
    Function.Injective (bridgeDiagonalRectangle hrect) := Fin.castLE_injective hrect

/-- The first 2d blocks of each stage serve the main diagonal; the next 2d
serve the antidiagonal. Labels outside this subset retain `otherChoice`. -/
def bridgeDiagonalChoice {J d L : ℕ} (hrect : J * (4 * d) ≤ L)
    (otherChoice : Fin L → Bool) : Fin L → Bool :=
  Function.extend (bridgeDiagonalRectangle hrect)
    (fun x => decide ((finProdFinEquiv.symm x : Fin J × Fin (4 * d)).2.val < 2 * d))
    otherChoice

theorem bridgeDiagonalChoice_at {J d L : ℕ} (hrect : J * (4 * d) ≤ L)
    (otherChoice : Fin L → Bool) (j : Fin J) (i : Fin (4 * d)) :
    bridgeDiagonalChoice hrect otherChoice
      (bridgeDiagonalRectangle hrect (finProdFinEquiv (j, i))) = decide (i.val < 2 * d) := by
  rw [bridgeDiagonalChoice, (bridgeDiagonalRectangle_injective hrect).extend_apply]
  simp

/-- Labels reserved for prefix or wide rectangles retain their requested
diagonal choice whenever they are outside the bridge label image. -/
theorem bridgeDiagonalChoice_outside {J d L : ℕ} (hrect : J * (4 * d) ≤ L)
    (otherChoice : Fin L → Bool) (x : Fin L)
    (hout : ¬ ∃ t, bridgeDiagonalRectangle hrect t = x) :
    bridgeDiagonalChoice hrect otherChoice x = otherChoice x := by
  exact Function.extend_apply' _ _ x hout

theorem bridgeDiagonalBlockSelect_at {J k d : ℕ} (hblocks : 4 * d ≤ k)
    (j : Fin J) (i : Fin (4 * d)) :
    bridgeDiagonalBlockSelect hblocks (finProdFinEquiv (j, i)) = (j, Fin.castLE hblocks i) := by
  simp [bridgeDiagonalBlockSelect]

/-- Exactly 2d indices per stage are assigned to each labelled diagonal. -/
theorem bridgeDiagonal_index_counts (d : ℕ) :
    ((Finset.univ : Finset (Fin (4 * d))).filter fun i => i.val < 2 * d).card = 2 * d ∧
    ((Finset.univ : Finset (Fin (4 * d))).filter fun i => ¬ i.val < 2 * d).card = 2 * d := by
  have hmain : ((Finset.univ : Finset (Fin (4 * d))).filter fun i => i.val < 2 * d).card = 2 * d := by
    rw [Fin.card_filter_val_lt]
    omega
  have htotal := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (4 * d))))
    (fun i => i.val < 2 * d)
  simp only [Finset.card_univ, Fintype.card_fin] at htotal
  exact ⟨hmain, by omega⟩

/-- In FC2K, Q=6(n+8), k=Q/2, and d=6, so all 4d diagonal blocks fit
within each stage's selected batch. -/
theorem fc2k_diagonal_blocks_fit (n : ℕ) (hn : 3 ≤ n) :
    4 * 6 ≤ (6 * (n + 8)) / 2 := by omega

/-- Install the explicitly allocated 4d bridge blocks per stage in a
joint RP1 packing. The remaining blocks stay outside this rectangle subset. -/
theorem install_allocated_bridge_diagonal_blocks (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (n : ℕ) (initial : Finset ℕ) (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (k J d L : ℕ) (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18) (hpositive : ∀ j < J, 0 < radii j)
    (hblocks : 4 * d ≤ k) (hrect : J * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (otherChoice : Fin L → Bool) (a : Cell n ≃ Fin (n * n))
    (reservedCells : Finset (Cell n))
    (hreserved : ∀ c ∈ reservedCells, entry a c ∈ initial)
    (hfree : ∀ t : Fin (J * (4 * d)), Disjoint
      (rectangleCells (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.firstColumn hs (bridgeDiagonalChoice hrect otherChoice)
          (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.secondColumn hs (bridgeDiagonalChoice hrect otherChoice)
          (bridgeDiagonalRectangle hrect t))) reservedCells) :
    ∃ a' : Cell n ≃ Fin (n * n),
      (∀ t side,
        entry a' (packedRectangleCorner hs (bridgeDiagonalChoice hrect otherChoice)
            (bridgeDiagonalRectangle hrect t, side)) =
          bridgeStageEndpoint n initial radii batches k J hvalid (bridgeDiagonalBlockSelect hblocks t, side)) ∧
      (∀ c ∈ reservedCells, entry a' c = entry a c) ∧
      (∀ t, 0 < selectedBridgeGap batches (bridgeDiagonalBlockSelect hblocks t).2
          (bridgeDiagonalBlockSelect hblocks t).1 ∧
        entry a' (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t),
            RectanglePacking.secondColumn hs (bridgeDiagonalChoice hrect otherChoice)
              (bridgeDiagonalRectangle hrect t)) =
          entry a' (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t),
            RectanglePacking.firstColumn hs (bridgeDiagonalChoice hrect otherChoice)
              (bridgeDiagonalRectangle hrect t)) +
                selectedBridgeGap batches (bridgeDiagonalBlockSelect hblocks t).2
                  (bridgeDiagonalBlockSelect hblocks t).1 ∧
        entry a' (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t),
            RectanglePacking.firstColumn hs (bridgeDiagonalChoice hrect otherChoice)
              (bridgeDiagonalRectangle hrect t)) =
          entry a' (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t),
            RectanglePacking.secondColumn hs (bridgeDiagonalChoice hrect otherChoice)
              (bridgeDiagonalRectangle hrect t)) +
                selectedBridgeGap batches (bridgeDiagonalBlockSelect hblocks t).2
                  (bridgeDiagonalBlockSelect hblocks t).1) :=
  install_selected_bridge_rectangles bmor upper n initial radii batches k J L (J * (4 * d))
    hvalid hn hnmax hpositive hs (bridgeDiagonalChoice hrect otherChoice)
    (bridgeDiagonalBlockSelect hblocks) (bridgeDiagonalBlockSelect_injective hblocks)
    (bridgeDiagonalRectangle hrect) (bridgeDiagonalRectangle_injective hrect)
    a reservedCells hreserved hfree

end
end Sude
