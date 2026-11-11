import Sude.FWGrowthSelectedDiagonalIdentity
import Sude.FWGrowthDiagonalAllocation

/-! The same allocated growth square carries both exact signed diagonal
contributions and the three-selection discrepancy invoice. -/
namespace Sude
noncomputable section

/-- Under the supplied narrowed trace, exact initial placement, balanced
choice and packed-layer hypotheses, one reallocation realizes the PD3--PD6
label families and their exact physical growth-image diagonal sums. The
remainder of each diagonal and all complete-line bounds remain separate. -/
theorem fw_growth_allocated_diagonal_contributions {n L : ℕ} {initial final : Finset ℕ}
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
        (0 < X/6 → |E3| < (3/2:ℝ)*(X/6)) := by
  classical
  dsimp only
  obtain ⟨T, U, V, ω, a', hsel, hmap, hperm, hfix, hstage, hgap, hbudget⟩ :=
    fw_growth_three_family_allocation trace hpool hn X hX hnarrow offset hoff hs choice rows cols hr hc a hplaced
  have hinj : Function.Injective (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc) :=
    (bt_growing_physical_stage_totals trace rfl hpool (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc a hplaced).1
  have hphysical := fw_growth_selected_diagonal_identities trace rfl hpool offset hoff hs hL choice
    rows cols hr hc reservedRows reservedCols hrows hcols hchoice a' ω T U
    (fun j => (hmap j).1) (fun j => (hmap j).2.1) hinj hperm
  exact ⟨T, U, V, ω, a', hsel, hmap, hperm, hfix, hstage, hgap, hphysical.1, hphysical.2, hbudget⟩

end
end Sude
