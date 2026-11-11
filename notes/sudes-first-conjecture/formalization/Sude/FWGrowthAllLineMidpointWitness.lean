import Sude.FWGrowthDiagonalOrdinaryRecentered
import Sude.FWGrowthFullMidpointBound
import Sude.FWGrowthPermutedTraceMidpoints

/-! A single trace-placed growth square with deterministic row/column midpoint
bounds. Diagonal estimates and full entry sums remain separate. -/
namespace Sude
noncomputable section
set_option maxHeartbeats 20000000

/-- From one supplied narrowed trace placement, produce one final square
which preserves the growth stage endpoint sets and gaps, fixes all other
cells, and satisfies the PD2 row/column midpoint bound about the original
stage means. The same chosen labels and final trace placement are retained. -/
theorem fw_growth_all_line_midpoint_witness {n L : ℕ} {initial final : Finset ℕ}
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
    let μ := fun j => (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) /
      (6*(n+8) : ℕ)
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
      (∀ j i, entry a' (cells ((j,i),true)) = entry a' (cells ((j,i),false)) + (stages.get j).gap) ∧
      (let E1 := (∑ j, ∑ p ∈ T j, growthStageMidpoint (stages.get j) p) - (12 : ℝ) * ∑ j, μ j
       let D2 := (∑ j, ∑ p ∈ U j, growthStageMidpoint (stages.get j) p) - (12 : ℝ) * ∑ j, μ j
       let E2 := (∑ j, ∑ p ∈ T j ∪ U j, growthStageMidpoint (stages.get j) p) - (24 : ℝ) * ∑ j, μ j
       let E3 := (∑ j, ∑ p ∈ (T j ∪ U j) ∪ V j, growthStageMidpoint (stages.get j) p) - (48 : ℝ) * ∑ j, μ j
       |E1| ≤ (X/6)/2 ∧ |D2| ≤ ((n+8 : ℝ)/(2*(n+6)))*(X/6) ∧
         |E2| ≤ ((n+5 : ℝ)/(n+6))*(X/6) ∧ |E3| ≤ (3/2:ℝ)*(X/6) ∧
         (0 < X/6 → |E3| < (3/2:ℝ)*(X/6))) ∧
      (∀ r : Fin n,
        |∑ s : Fin stages.length × Fin (6*(n+8)),
          physicalPairLineWeight cells (fun c => c.1 = r) s *
            ((((entry a' (cells (s,true)) : ℝ) + entry a' (cells (s,false))) / 2) - μ s.1)| ≤
          (Nat.clog 2 (6*n) : ℝ) * (8*(X/6)) + 3*(X/6)/(n : ℝ) + 2*(X/6)) ∧
      (∀ c : Fin n,
        |∑ s : Fin stages.length × Fin (6*(n+8)),
          physicalPairLineWeight cells (fun q => q.2 = c) s *
            ((((entry a' (cells (s,true)) : ℝ) + entry a' (cells (s,false))) / 2) - μ s.1)| ≤
          (Nat.clog 2 (6*n) : ℝ) * (8*(X/6)) + 3*(X/6)/(n : ℝ) + 2*(X/6)) := by
  classical
  dsimp only
  let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
    offset hoff hs choice rows cols hr hc
  obtain ⟨T, U, V, ω₀, ω, a₀, a', hsel, hmap₀, hmap, hperm₀, hperm, hnon, hωsame,
    hfix, hstage, hgap, hbudget, hDP, hrowcol⟩ :=
    fw_growth_diagonal_ordinary_recentered trace hpool hn X hX hnarrow offset hoff hs choice rows cols hr hc
      reservedRows reservedCols hrows hcols a hplaced
  have hmidall := (growth_permuted_trace_midpoints trace rfl hpool cells a' ω hperm).2.2
  have hmid : ∀ (j : Fin stages.length) (rect : Fin (4*6)) (pair : Fin 2),
      let i := prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (rect,pair)
      (((entry a' (cells ((j,i),true)) : ℝ) + entry a' (cells ((j,i),false))) / 2) =
        growthStageMidpoint (stages.get j) (trace.lowAt rfl j (ω j i)) := by
    intro j rect pair
    let i := prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (rect,pair)
    change (((entry a' (cells ((j,i),true)) : ℝ) + entry a' (cells ((j,i),false))) / 2) =
      growthStageMidpoint (stages.get j) (trace.lowAt rfl j (ω j i))
    have h := hmidall j i
    change (((entry a' (cells ((j,i),false)) : ℝ) + entry a' (cells ((j,i),true))) / 2) =
      growthStageMidpoint (stages.get j) (trace.lowAt rfl j (ω j i)) at h
    rw [add_comm ((entry a' (cells ((j,i),true)) : ℝ)) ((entry a' (cells ((j,i),false)) : ℝ))]
    exact h
  have hfull := fw_growth_full_midpoint_bound (by omega) trace X hX hnarrow ω₀ ω T U V
    hmap₀ hsel hbudget.2.2.2.1 offset hoff hs choice rows cols hr hc a' hmid hDP
  exact ⟨T, U, V, ω, a', hsel, hmap, hperm, hfix, hstage, hgap, hbudget, hfull.1, hfull.2⟩

end
end Sude
