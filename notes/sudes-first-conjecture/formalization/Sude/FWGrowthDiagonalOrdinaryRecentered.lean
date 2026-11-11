import Sude.FWGrowthOrdinaryRecenterLineBound

namespace Sude
noncomputable section
set_option maxHeartbeats 5000000

/-- Starting from one trace-placed square, select the diagonal/partner labels
and rebalance the ordinary labels on one final square. The final ordinary
row and column midpoint contributions are centered at the original stage
means. Rectangle contributions, diagonal bounds and complete lines are
separate obligations. -/
theorem fw_growth_diagonal_ordinary_recentered {n L : ℕ} {initial final : Finset ℕ}
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
    (a : Cell n ≃ Fin (n*n))
    (hplaced : ∀ x : PrefixPhysicalInputs stages.length 6 3 n,
      entry a (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x) =
        (trace.poolValues rfl hpool (prefixPhysicalInput (by omega) (by omega) x)).val) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    let pop := fwGrowthOrdinaryPopulation n stages.length
    let originalMean := 12 * ∑ j, ((∑ p ∈ (stages.get j).lows,
      growthStageMidpoint (stages.get j) p) / (6*(n+8) : ℕ))
    ∃ (T U V : Fin stages.length → Finset ℕ)
      (ω₀ ω : Fin stages.length → Equiv.Perm (Fin (6*(n+8))))
      (a₀ a' : Cell n ≃ Fin (n*n)),
      (∀ j, T j ⊆ (stages.get j).lows ∧ U j ⊆ (stages.get j).lows \ T j ∧
        V j ⊆ (stages.get j).lows \ (T j ∪ U j) ∧
        (T j).card = 12 ∧ (U j).card = 12 ∧ (V j).card = 24) ∧
      (∀ j, (fwGrowthMainSlots n).image (fun i => trace.lowAt rfl j (ω₀ j i)) = T j ∧
        (fwGrowthAntiSlots n).image (fun i => trace.lowAt rfl j (ω₀ j i)) = U j ∧
        (fwGrowthPartnerSlots n).image (fun i => trace.lowAt rfl j (ω₀ j i)) = V j) ∧
      (∀ j, (fwGrowthMainSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = T j ∧
        (fwGrowthAntiSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = U j ∧
        (fwGrowthPartnerSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = V j) ∧
      (∀ x, entry a₀ (cells x) = (trace.poolValues rfl hpool (stagePairPermutation ω₀ x)).val) ∧
      (∀ x, entry a' (cells x) = (trace.poolValues rfl hpool (stagePairPermutation ω x)).val) ∧
      (∀ j i, i ∉ fwGrowthOrdinarySlots n → ∀ side,
        entry a' (cells ((j,i),side)) = entry a₀ (cells ((j,i),side))) ∧
      (∀ j i, i ∉ fwGrowthOrdinarySlots n → ω j i = ω₀ j i) ∧
      (∀ c, c ∉ Set.range cells → entry a' c = entry a c) ∧
      (∀ j, Finset.univ.image (fun x : Fin (6*(n+8)) × Bool => entry a' (cells ((j,x.1),x.2))) =
        Finset.univ.image (fun x : Fin (6*(n+8)) × Bool => entry a (cells ((j,x.1),x.2)))) ∧
      (∀ j i, entry a' (cells ((j,i),true)) = entry a' (cells ((j,i),false)) + (stages.get j).gap) ∧
      (let μ := fun j => (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) /
        (6 * (n+8) : ℕ)
       let E1 := (∑ j, ∑ p ∈ T j, growthStageMidpoint (stages.get j) p) - (12 : ℝ) * ∑ j, μ j
       let D2 := (∑ j, ∑ p ∈ U j, growthStageMidpoint (stages.get j) p) - (12 : ℝ) * ∑ j, μ j
       let E2 := (∑ j, ∑ p ∈ T j ∪ U j, growthStageMidpoint (stages.get j) p) - (24 : ℝ) * ∑ j, μ j
       let E3 := (∑ j, ∑ p ∈ (T j ∪ U j) ∪ V j, growthStageMidpoint (stages.get j) p) - (48 : ℝ) * ∑ j, μ j
       |E1| ≤ (X/6)/2 ∧ |D2| ≤ ((n+8 : ℝ)/(2*(n+6)))*(X/6) ∧
         |E2| ≤ ((n+5 : ℝ)/(n+6))*(X/6) ∧ |E3| ≤ (3/2:ℝ)*(X/6) ∧
         (0 < X/6 → |E3| < (3/2:ℝ)*(X/6))) ∧
      (let midpoint := fun s : Fin stages.length × Fin (6*(n+8)) =>
        growthStageMidpoint (stages.get s.1) (trace.lowAt rfl s.1 (ω₀ s.1 s.2))
       ∀ l : Fin ((n+n)+2),
        |(∑ s : {s // s ∈ pop}, physicalPairLineWeight cells
            (fun c => c ∈ physicalAllLineCells l) s.val *
            (((entry a' (cells (s.val,true)) : ℝ) + entry a' (cells (s.val,false))) / 2)) -
          ∑ j ∈ pop.image Prod.fst,
            (∑ s ∈ pop.filter (fun s => s.1 = j), physicalPairLineWeight cells
              (fun c => c ∈ physicalAllLineCells l) s) *
                prefixOriginalStageMean pop Prod.fst midpoint j| ≤
          (Nat.clog 2 (6*n) : ℝ) * (8 * (X/6))) ∧
      (∀ l ∈ (Finset.univ.image fwGrowthRowLineLabel ∪ Finset.univ.image fwGrowthColumnLineLabel :
        Finset (Fin ((n+n)+2))),
        |(∑ s : {s // s ∈ pop}, physicalPairLineWeight cells
            (fun c => c ∈ physicalAllLineCells l) s.val *
            (((entry a' (cells (s.val,true)) : ℝ) + entry a' (cells (s.val,false))) / 2)) - originalMean| ≤
          (Nat.clog 2 (6*n) : ℝ) * (8 * (X/6)) + 3*(X/6)/(n : ℝ)) := by
  classical
  dsimp only
  obtain ⟨T, U, V, ω₀, ω, a₀, a', e, hsel, hmap₀, hperm₀, hperm, he, hentry, hfix,
    hnon, hωsame, hmap, hfixall, hstage, hgap, hbudget, hbound⟩ :=
    fw_growth_diagonal_ordinary_trace_dp trace hpool hn X hX hnarrow offset hoff hs choice rows cols hr hc
      reservedRows reservedCols hrows hcols a hplaced
  have hrowcol := fw_growth_ordinary_recentered_rows_columns (by omega) trace ω₀ T U V X
    hmap₀ hsel hbudget.2.2.2.1 offset hoff hs choice rows cols hr hc a' hbound
  exact ⟨T, U, V, ω₀, ω, a₀, a', hsel, hmap₀, hmap, hperm₀, hperm, hnon, hωsame,
    hfixall, hstage, hgap, hbudget, hbound, hrowcol⟩

end
end Sude
