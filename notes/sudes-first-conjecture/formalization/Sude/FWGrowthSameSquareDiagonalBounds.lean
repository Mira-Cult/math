import Sude.FWGrowthSelectedDiagonalIdentity
import Sude.FWGrowthPermutedTraceMidpoints

/-! Transfer selected growth diagonal invoices to a supplied final square.
No square construction or complete-diagonal estimate is asserted here. -/
namespace Sude
noncomputable section

/-- For one supplied final trace placement, the selected growth-image diagonal
contributions satisfy the stated E1 and D2 bounds about their common signed
gap reference. The remainder of each diagonal is not included. -/
theorem fw_growth_same_square_diagonal_bounds {n L : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6*(n+8)) initial radius final last stages)
    (hpool : ∀ p ∈ initial, p ∈ pool n)
    (offset : ℕ) (hoff : offset + stages.length*(4*6) ≤ L) (hs : 2*L+1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = stages.length*3) (hc : cols.length = stages.length*3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows rows)
    (hcols : LayerPacking.PackedLayers reservedCols cols)
    (hchoice : ∀ j rect, choice (btGrowingOffsetRectangle offset hoff (finProdFinEquiv (j,rect))) = decide (rect.val < 12))
    (a : Cell n ≃ Fin (n*n)) (ω : Fin stages.length → Equiv.Perm (Fin (6*(n+8))))
    (T U : Fin stages.length → Finset ℕ) (X : ℝ)
    (hmain : ∀ j, (fwGrowthMainSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = T j)
    (hanti : ∀ j, (fwGrowthAntiSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = U j)
    (hplaced : ∀ x, entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc x) = (trace.poolValues rfl hpool (stagePairPermutation ω x)).val)
    (hE1 : |(∑ j, ∑ p ∈ T j, growthStageMidpoint (stages.get j) p) - (12 : ℝ) *
      ∑ j, ((∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) / (6*(n+8) : ℕ))| ≤ (X/6)/2)
    (hD2 : |(∑ j, ∑ p ∈ U j, growthStageMidpoint (stages.get j) p) - (12 : ℝ) *
      ∑ j, ((∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) / (6*(n+8) : ℕ))| ≤
        ((n+8 : ℝ)/(2*(n+6)))*(X/6)) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    let μ := fun j => (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) /
      (6*(n+8) : ℕ)
    ((∑ c ∈ (Finset.univ.image cells).filter (fun c => c ∈ mainCells n), (entry a c : ℝ)) =
      (∑ j, ∑ p ∈ T j, growthStageMidpoint (stages.get j) p) -
        6 * ∑ j, ((stages.get j).gap : ℝ)) ∧
    ((∑ c ∈ (Finset.univ.image cells).filter (fun c => c ∈ antiCells n), (entry a c : ℝ)) =
      (∑ j, ∑ p ∈ U j, growthStageMidpoint (stages.get j) p) -
        6 * ∑ j, ((stages.get j).gap : ℝ)) ∧
    |(∑ c ∈ (Finset.univ.image cells).filter (fun c => c ∈ mainCells n), (entry a c : ℝ)) -
      ((12 : ℝ) * ∑ j, μ j - 6 * ∑ j, ((stages.get j).gap : ℝ))| ≤ (X/6)/2 ∧
    |(∑ c ∈ (Finset.univ.image cells).filter (fun c => c ∈ antiCells n), (entry a c : ℝ)) -
      ((12 : ℝ) * ∑ j, μ j - 6 * ∑ j, ((stages.get j).gap : ℝ))| ≤
        ((n+8 : ℝ)/(2*(n+6)))*(X/6) := by
  classical
  dsimp only
  let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
    offset hoff hs choice rows cols hr hc
  let μ := fun j => (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) /
    (6*(n+8) : ℕ)
  have hcells : Function.Injective cells :=
    (growth_permuted_trace_midpoints trace rfl hpool cells a ω hplaced).1
  have hid := fw_growth_selected_diagonal_identities trace rfl hpool offset hoff hs hL choice
    rows cols hr hc reservedRows reservedCols hrows hcols hchoice a ω T U hmain hanti hcells hplaced
  simp only [BTStageTrace.stageAt, Fin.cast_eq_self] at hid
  have hmain' := hid.1
  have hanti' := hid.2
  refine ⟨hmain', hanti', ?_, ?_⟩
  · rw [hmain', sub_sub_sub_cancel_right]
    exact hE1
  · rw [hanti', sub_sub_sub_cancel_right]
    exact hD2

end
end Sude
