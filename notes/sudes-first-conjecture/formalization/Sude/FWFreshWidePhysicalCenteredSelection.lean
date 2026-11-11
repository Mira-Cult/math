import Sude.FWFreshWideMidpointGapSelection
import Sude.FWWideBalancedPhysicalCenteredGap

/-! A fresh simultaneous selection is reallocated to one actual square.
Only the centered selected-rectangle contrast is controlled; midpoint and
spare contributions, earlier witnesses, and prime targets remain separate. -/
namespace Sude
noncomputable section

/-- Fresh wide midpoint and centered physical-gap control on one square. -/
theorem fw_fresh_wide_physical_centered_selection {n L P m : ℕ}
    (hn : 450 ≤ n) (hm : 0 < m)
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (other : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (μ X : ℝ) (hX : (100 : ℝ) ≤ X)
    (hmlo : (243/500 : ℝ)*X ≤ μ) (hmhi : μ ≤ (123/250 : ℝ)*X)
    (blocks : List DoublePair) (hlen : blocks.length = (3*(n/450))*(3*(n+8)))
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft μ X) (fwReflectedRight μ X))
      (bmorHighBins (fwReflectedLeft μ X) (fwReflectedRight μ X)))
    (old : Cell n ≃ Fin (n*n))
    (hplaced : ∀ x : FWWideInputs n,
      entry old (fwWidePhysicalCells hwide hs
        (fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth other) rows cols hr hc x) =
      doublePairSequenceEndpoint blocks
        (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2))
    (hinj : Function.Injective (fwWidePhysicalDoubleCells hwide hs
      (fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth other) rows cols hr hc))
    (line : Fin m → Cell n → Prop) (V : ℝ) (hV : 0 < V)
    (lo hi : Fin (3*(n/450)) → ℝ)
    (hinterval : ∀ j b p,
      doubleBlockPairMidpoint (fwWidePhysicalDoubleCells hwide hs
        (fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth other) rows cols hr hc)
        old j b p ∈ Set.Icc (lo j) (hi j))
    (hinvoice : ∀ l, doubleBlockCombinedProxy
      (fwWidePhysicalDoubleCells hwide hs
        (fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth other) rows cols hr hc)
        (line l) lo hi ≤ V/4) :
    let choice := fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth other
    let cells := fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc
    let gap := fun j b => fwPermutedWideSourceGap blocks hlen (fun _ => Equiv.refl _) j b
    let E := Real.sqrt (V * Real.log (4 * (m : ℝ)) / 2)
    let T := 2 * Real.sqrt ((3/2 : ℝ) * ((3*(n/450) : ℕ) : ℝ) * ((64/235 : ℝ)*X)^2 * Real.log 16)
    let label := fun j side r => fwWideRectangle hwide (finProdFinEquiv (j, fwWideSignedGapRectangle side r))
    ∃ (π : Fin (3*(n/450)) → Equiv.Perm (Fin (3*(n+8))))
      (swaps : (Fin (3*(n/450)) × Fin (3*(n+8))) → Bool)
      (a : Cell n ≃ Fin (n*n)),
      (∀ l, |doubleBlockSampleScore cells (line l) old π swaps| < E) ∧
      (∀ j b p side, entry a (cells ((j,b,p),side)) =
        entry old (cells ((j,π j b,doubleBlockPairSwap (swaps (j,b)) p),side))) ∧
      (∀ c, c ∉ Set.range cells → entry a c = entry old c) ∧
      (∀ j side r, (if side = true then packedRectangleCorner hs choice (label j side r,0) ∈ mainCells n
        else packedRectangleCorner hs choice (label j side r,0) ∈ antiCells n)) ∧
      (∀ j side, (∑ r : Fin 12,
       ((entry a (packedRectangleCorner hs choice (label j side r,0)) : ℝ) -
        ((entry a (packedRectangleCorner hs choice (label j side r,0)) : ℝ) +
         (entry a (packedRectangleCorner hs choice (label j side r,1)) : ℝ))/2)) =
       -(1/2 : ℝ) * ∑ b ∈ fwWideSignedGapSlots n side, (gap j (π j b) : ℝ)) ∧
      |(1/2 : ℝ) * ((∑ j, ∑ b ∈ fwWideSignedGapSlots n true, (gap j (π j b) : ℝ)) -
        ∑ j, ∑ b ∈ fwWideSignedGapSlots n false, (gap j (π j b) : ℝ))| < T := by
  classical
  dsimp only
  let choice := fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth other
  let cells := fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc
  let gap := fun j b => fwPermutedWideSourceGap blocks hlen (fun _ => Equiv.refl _) j b
  have hsel := fw_fresh_wide_midpoint_gap_selection hn hm hwide hs choice rows cols hr hc
    μ X hX hmlo hmhi blocks hlen hmatched old hplaced line V hV lo hi hinterval hinvoice
  dsimp only at hsel
  obtain ⟨holdgap, π, swaps, hscore, hbound⟩ := hsel
  obtain ⟨a, hentry, hfixed, _, hnewgap⟩ := reallocate_existing_stage_double_blocks old cells hinj π
    (fun j b => doubleBlockPairSwap (swaps (j,b)))
  have hg : ∀ j b, (entry a (cells ((j,b,0),true)) : ℝ) =
      (entry a (cells ((j,b,0),false)) : ℝ) + (gap j (π j b) : ℝ) := by
    intro j b
    exact_mod_cast hnewgap gap holdgap j b 0
  have hgeom := fw_wide_balanced_physical_centered_gap hrect hseed hwide hgrowth hs other
    rows cols hr hc a π (fun j b => (gap j b : ℝ)) hg
  dsimp only at hgeom
  exact ⟨π, swaps, a, hscore, hentry, hfixed, hgeom.1, hgeom.2, hbound⟩
end
end Sude
