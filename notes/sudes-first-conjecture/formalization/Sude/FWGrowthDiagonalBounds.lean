import Sude.FWGrowthAllocatedDiagonals

/-! Bounds for the allocated growth image's diagonal contributions. -/
namespace Sude
noncomputable section

/-- On the same selected and reallocated square, the growth-image main and
antidiagonal contributions satisfy the PD3/PD4 bounds around their signed
common-gap reference. No bound on the rest of either diagonal is asserted. -/
theorem fw_growth_allocated_diagonal_bounds {n L : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6*(n+8)) initial radius final last stages)
    (hpool : ∀ p ∈ initial, p ∈ pool n) (hn : 3 ≤ n)
    (X : ℝ) (hX : 0 ≤ X) (hnarrow : NarrowedStages (X/6) stages)
    (offset : ℕ) (hoff : offset + stages.length*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = stages.length*3) (hc : cols.length = stages.length*3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows rows)
    (hcols : LayerPacking.PackedLayers reservedCols cols)
    (hL : 3 ≤ L)
    (hchoice : ∀ j rect, choice (btGrowingOffsetRectangle offset hoff (finProdFinEquiv (j,rect))) = decide (rect.val < 12))
    (a : Cell n ≃ Fin (n*n))
    (hplaced : ∀ x : PrefixPhysicalInputs stages.length 6 3 n,
      entry a (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x) =
        (trace.poolValues rfl hpool (prefixPhysicalInput (by omega) (by omega) x)).val) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    ∃ (T U V : Fin stages.length → Finset ℕ)
      (ω : Fin stages.length → Equiv.Perm (Fin (6*(n+8)))) (a' : Cell n ≃ Fin (n*n)),
      (∀ j, T j ⊆ (stages.get j).lows ∧ U j ⊆ (stages.get j).lows \ T j ∧
        V j ⊆ (stages.get j).lows \ (T j ∪ U j) ∧
        (T j).card = 12 ∧ (U j).card = 12 ∧ (V j).card = 24) ∧
      (∀ j, (fwGrowthMainSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = T j ∧
        (fwGrowthAntiSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = U j ∧
        (fwGrowthPartnerSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = V j) ∧
      (∀ x, entry a' (cells x) = (trace.poolValues rfl hpool (stagePairPermutation ω x)).val) ∧
      (∀ c, c ∉ Set.range cells → entry a' c = entry a c) ∧
      (∀ j, Finset.univ.image (fun x : Fin (6*(n+8)) × Bool => entry a' (cells ((j,x.1),x.2))) =
        Finset.univ.image (fun x : Fin (6*(n+8)) × Bool => entry a (cells ((j,x.1),x.2)))) ∧
      (∀ j i, entry a' (cells ((j,i),true)) =
        entry a' (cells ((j,i),false)) + (stages.get j).gap) ∧
      ((∑ c ∈ (Finset.univ.image cells).filter (fun c => c ∈ mainCells n), (entry a' c : ℝ)) =
        (∑ j, ∑ p ∈ T j, growthStageMidpoint (stages.get j) p) -
          6 * ∑ j, ((stages.get j).gap : ℝ)) ∧
      ((∑ c ∈ (Finset.univ.image cells).filter (fun c => c ∈ antiCells n), (entry a' c : ℝ)) =
        (∑ j, ∑ p ∈ U j, growthStageMidpoint (stages.get j) p) -
          6 * ∑ j, ((stages.get j).gap : ℝ)) ∧
      let μ := fun j => (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) /
        (6 * (n+8) : ℕ)
      let E1 := (∑ j, ∑ p ∈ T j, growthStageMidpoint (stages.get j) p) - (12 : ℝ) * ∑ j, μ j
      let D2 := (∑ j, ∑ p ∈ U j, growthStageMidpoint (stages.get j) p) - (12 : ℝ) * ∑ j, μ j
      let E2 := (∑ j, ∑ p ∈ T j ∪ U j, growthStageMidpoint (stages.get j) p) - (24 : ℝ) * ∑ j, μ j
      let E3 := (∑ j, ∑ p ∈ (T j ∪ U j) ∪ V j, growthStageMidpoint (stages.get j) p) - (48 : ℝ) * ∑ j, μ j
      |E1| ≤ (X/6)/2 ∧ |D2| ≤ ((n+8 : ℝ)/(2*(n+6)))*(X/6) ∧
        |E2| ≤ ((n+5 : ℝ)/(n+6))*(X/6) ∧ |E3| ≤ (3/2:ℝ)*(X/6) ∧
        (0 < X/6 → |E3| < (3/2:ℝ)*(X/6)) ∧
        |(∑ c ∈ (Finset.univ.image cells).filter (fun c => c ∈ mainCells n), (entry a' c : ℝ)) -
          ((12 : ℝ) * ∑ j, μ j - 6 * ∑ j, ((stages.get j).gap : ℝ))| ≤ (X/6)/2 ∧
        |(∑ c ∈ (Finset.univ.image cells).filter (fun c => c ∈ antiCells n), (entry a' c : ℝ)) -
          ((12 : ℝ) * ∑ j, μ j - 6 * ∑ j, ((stages.get j).gap : ℝ))| ≤ ((n+8 : ℝ)/(2*(n+6)))*(X/6) := by
  classical
  dsimp only
  obtain ⟨T, U, V, ω, a', hsel, hmap, hperm, hfix, hstage, hgap, hmain, hanti, hbudget⟩ :=
    fw_growth_allocated_diagonal_contributions trace hpool hn X hX hnarrow offset hoff hs choice
      rows cols hr hc reservedRows reservedCols hrows hcols hL hchoice a hplaced
  dsimp only at hbudget
  let μ := fun j => (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) /
    (6 * (n+8) : ℕ)
  have hbmain : |(∑ c ∈ (Finset.univ.image
      (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        offset hoff hs choice rows cols hr hc)).filter (fun c => c ∈ mainCells n), (entry a' c : ℝ)) -
      ((12 : ℝ) * ∑ j, μ j - 6 * ∑ j, ((stages.get j).gap : ℝ))| ≤ (X/6)/2 := by
    rw [hmain]
    convert hbudget.1 using 1 <;> dsimp [μ] <;> congr 1 <;> ring
  have hbanti : |(∑ c ∈ (Finset.univ.image
      (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        offset hoff hs choice rows cols hr hc)).filter (fun c => c ∈ antiCells n), (entry a' c : ℝ)) -
      ((12 : ℝ) * ∑ j, μ j - 6 * ∑ j, ((stages.get j).gap : ℝ))| ≤
      ((n+8 : ℝ)/(2*(n+6)))*(X/6) := by
    rw [hanti]
    convert hbudget.2.1 using 1 <;> dsimp [μ] <;> congr 1 <;> ring
  exact ⟨T, U, V, ω, a', hsel, hmap, hperm, hfix, hstage, hgap, hmain, hanti,
    hbudget.1, hbudget.2.1, hbudget.2.2.1, hbudget.2.2.2.1, hbudget.2.2.2.2, hbmain, hbanti⟩

end
end Sude
