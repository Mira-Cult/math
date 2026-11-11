import Sude.GrowthTraceDiagonalIdentity
import Sude.FWGrowthFullDiagonalOrientation
import Sude.FWGrowthFullDiagonalWeights

/-! Both exact diagonal contributions for an already allocated growth trace. -/
namespace Sude
noncomputable section

/-- On the supplied square with the same permuted growth trace, balanced
rectangle choice and packed layers turn the selected source midpoint sums
into exact growth-image diagonal contributions, with the signed `-6` times
the stage-gap sum. Other cells on either diagonal are not included. -/
theorem fw_growth_selected_diagonal_identities {n P L : ℕ}
    {initial final : Finset ℕ} {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6*(n+8)) initial radius final last stages)
    (hlen : stages.length = P) (hpool : ∀ p ∈ initial, p ∈ pool n)
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P*3) (hc : cols.length = P*3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows rows)
    (hcols : LayerPacking.PackedLayers reservedCols cols)
    (hchoice : ∀ j rect, choice (btGrowingOffsetRectangle offset hoff (finProdFinEquiv (j,rect))) = decide (rect.val < 12))
    (a : Cell n ≃ Fin (n*n)) (ω : Fin P → Equiv.Perm (Fin (6*(n+8))))
    (T U : Fin P → Finset ℕ)
    (hmain : ∀ j, (fwGrowthMainSlots n).image (fun i => trace.lowAt hlen j (ω j i)) = T j)
    (hanti : ∀ j, (fwGrowthAntiSlots n).image (fun i => trace.lowAt hlen j (ω j i)) = U j)
    (hcells : Function.Injective (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc))
    (hplaced : ∀ x, entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc x) = (trace.poolValues hlen hpool (stagePairPermutation ω x)).val) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    (∑ c ∈ (Finset.univ.image cells).filter (fun c => c ∈ mainCells n), (entry a c : ℝ)) =
      (∑ j, ∑ p ∈ T j, growthStageMidpoint (BTStageTrace.stageAt stages hlen j) p) -
        6 * ∑ j, ((BTStageTrace.stageAt stages hlen j).gap : ℝ) ∧
    (∑ c ∈ (Finset.univ.image cells).filter (fun c => c ∈ antiCells n), (entry a c : ℝ)) =
      (∑ j, ∑ p ∈ U j, growthStageMidpoint (BTStageTrace.stageAt stages hlen j) p) -
        6 * ∑ j, ((BTStageTrace.stageAt stages hlen j).gap : ℝ) := by
  classical
  dsimp only
  constructor
  · apply growth_trace_selected_diagonal_identity trace hlen hpool _ hcells (fun c => c ∈ mainCells n)
      a ω (fun _ => fwGrowthMainSlots n) T hmain (fun _ => (fw_growth_slot_group_cardinalities n).1)
    · intro j i
      exact (fw_growth_full_diagonal_weights offset hoff hs hL choice rows cols hr hc reservedRows reservedCols
        hrows hcols j (hchoice j) i).1
    · intro j i
      exact (fw_growth_full_diagonal_orientation offset hoff hs hL choice rows cols hr hc reservedRows reservedCols
        hrows hcols j i).1
    · exact hplaced
  · apply growth_trace_selected_diagonal_identity trace hlen hpool _ hcells (fun c => c ∈ antiCells n)
      a ω (fun _ => fwGrowthAntiSlots n) U hanti (fun _ => (fw_growth_slot_group_cardinalities n).2.1)
    · intro j i
      exact (fw_growth_full_diagonal_weights offset hoff hs hL choice rows cols hr hc reservedRows reservedCols
        hrows hcols j (hchoice j) i).2
    · intro j i
      exact (fw_growth_full_diagonal_orientation offset hoff hs hL choice rows cols hr hc reservedRows reservedCols
        hrows hcols j i).2
    · exact hplaced

end
end Sude
