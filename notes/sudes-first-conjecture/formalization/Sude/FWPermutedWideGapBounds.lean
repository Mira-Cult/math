import Sude.FWPermutedOrdinaryEdgeGaps
import Sude.FWMatchedBlockGeometry

/-! Bounds for stage-permuted source gaps from reflected-bin matched blocks.
No grid, crossing, or physical placement is constructed. -/

namespace Sude
noncomputable section

/-- The exact gap of a reflected-bin matched block is positive, even and
in the source interval. No square placement is needed. -/
theorem fw_matched_block_source_gap_bounds (μ X : ℝ) (hX : 100 ≤ X)
    (hmlo : (243 / 500 : ℝ) * X ≤ μ) (hmhi : μ ≤ (123 / 250 : ℝ) * X)
    (block : DoublePair)
    (hmatched : block.MatchedValid
      (bmorLowBins (fwReflectedLeft μ X) (fwReflectedRight μ X))
      (bmorHighBins (fwReflectedLeft μ X) (fwReflectedRight μ X))) :
    let gap := block.high₁ - block.low₁
    0 < gap ∧ 2 ∣ gap ∧ (2 / 3 : ℝ) * X ≤ (gap : ℝ) ∧ (gap : ℝ) < X := by
  dsimp only
  obtain ⟨i, hlo, hhi⟩ := hmatched.2.1
  have hlow : (block.low₁ : ℤ) % 2 = 1 := by
    change block.low₁ ∈ apInterval (fwReflectedLeft μ X (i,false))
      (fwReflectedRight μ X (i,false)) 2 1 at hlo
    have h := (Finset.mem_filter.mp hlo).2.2
    norm_num at h ⊢
    exact h
  have hhigh : (block.high₁ : ℤ) % 2 = 1 := by
    change block.high₁ ∈ apInterval (fwReflectedLeft μ X (i,true))
      (fwReflectedRight μ X (i,true)) 2 1 at hhi
    have h := (Finset.mem_filter.mp hhi).2.2
    norm_num at h ⊢
    exact h
  obtain ⟨_, _, _, _, _, _, horder, _, _⟩ := hmatched.1
  have hgeom := fw_matched_block_pair_bounds μ X hX hmlo hmhi block hmatched
  have hcast : ((block.high₁ - block.low₁ : ℕ) : ℝ) = (block.high₁ : ℝ) - block.low₁ := by
    rw [Nat.cast_sub (Nat.le_of_lt horder)]
  have heven : 2 ∣ block.high₁ - block.low₁ := by omega
  have hpositive : 0 < block.high₁ - block.low₁ := by omega
  refine ⟨hpositive, heven, ?_, ?_⟩
  · rw [hcast]; exact hgeom.2.1
  · rw [hcast]; nlinarith [hgeom.2.2.1]

/-- Source gap selected by the stage-wise wide block permutation. -/
def fwPermutedWideSourceGap {n : ℕ} (blocks : List DoublePair)
    (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (π : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (j : Fin (3 * (n / 450))) (b : Fin (3 * (n + 8))) : ℕ :=
  let source := blocks.get (Fin.cast hlen.symm (finProdFinEquiv (j, π j b)))
  source.high₁ - source.low₁

/-- Stage permutation selects another actual matched block, so every
source-indexed gap has the same parity and quantitative bounds. -/
theorem fw_permuted_wide_source_gap_bounds {n : ℕ}
    (μ X : ℝ) (hX : 100 ≤ X)
    (hmlo : (243 / 500 : ℝ) * X ≤ μ) (hmhi : μ ≤ (123 / 250 : ℝ) * X)
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft μ X) (fwReflectedRight μ X))
      (bmorHighBins (fwReflectedLeft μ X) (fwReflectedRight μ X)))
    (π : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (j : Fin (3 * (n / 450))) (b : Fin (3 * (n + 8))) :
    let gap := fwPermutedWideSourceGap blocks hlen π j b
    0 < gap ∧ 2 ∣ gap ∧ (2 / 3 : ℝ) * X ≤ (gap : ℝ) ∧ (gap : ℝ) < X := by
  dsimp [fwPermutedWideSourceGap]
  exact fw_matched_block_source_gap_bounds μ X hX hmlo hmhi _
    (hmatched _ (List.get_mem _ _))


/-- The reallocated ordinary edge on both physical networks has the exact
permuted source gap, with its matched-bin bounds. -/
theorem fw_permuted_wide_edge_gap_bounds {n L : ℕ}
    (μ X : ℝ) (hX : 100 ≤ X)
    (hmlo : (243 / 500 : ℝ) * X ≤ μ) (hmhi : μ ≤ (123 / 250 : ℝ) * X)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft μ X) (fwReflectedRight μ X))
      (bmorHighBins (fwReflectedLeft μ X) (fwReflectedRight μ X)))
    (new : Cell n ≃ Fin (n*n))
    (π : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (hgap : ∀ j b p, entry new (fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc ((j,b,p),true)) =
      entry new (fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc ((j,b,p),false)) +
        fwPermutedWideSourceGap blocks hlen π j b)
    (j : Fin (3 * (n / 450))) (edge : Fin 3 × Fin n) :
    let gap := fwPermutedWideSourceGap blocks hlen π j
      (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge)
    0 < gap ∧ 2 ∣ gap ∧ (2 / 3 : ℝ) * X ≤ (gap : ℝ) ∧ (gap : ℝ) < X ∧
      ∀ network : Bool,
        entry new (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
          entry new (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j edge.1 edge.2 network false)) + gap := by
  dsimp only
  have hbounds := fw_permuted_wide_source_gap_bounds μ X hX hmlo hmhi blocks hlen hmatched π j
    (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge)
  refine ⟨hbounds.1, hbounds.2.1, hbounds.2.2.1, hbounds.2.2.2, ?_⟩
  intro network
  exact fw_permuted_wide_ordinary_edge_gap hwide hs choice rows cols hr hc blocks hlen new π
    (by simpa only [fwPermutedWideSourceGap] using hgap) j edge network

end
end Sude
