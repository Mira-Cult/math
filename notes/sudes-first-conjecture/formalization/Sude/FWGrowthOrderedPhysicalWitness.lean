import Sude.FWGrowthAllLineMidpointWitness
import Sude.FWGrowthTracePhysicalEntryBound

/-! Ordered same-witness physical growth row/column contributions. The full
nongrowth residual and actual incidence-weighted stage baseline stay explicit.
This does not transfer the result across later centering switches. -/
namespace Sude
noncomputable section
set_option maxHeartbeats 2000000

/-- From one narrowed trace placement, choose one final square and retain
both its growth midpoint bounds and the corresponding physical-entry bounds.
Every nongrowth line cell remains in the explicit residual. -/
theorem fw_growth_ordered_physical_entry_witness {n L : ℕ} {initial final : Finset ℕ}
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
          (Nat.clog 2 (6*n) : ℝ) * (8*(X/6)) + 3*(X/6)/(n : ℝ) + 2*(X/6)) ∧
      (∀ r : Fin n, |(∑ c ∈ rowCells r, (entry a' c : ℝ)) -
        (∑ c ∈ rowCells r \ Finset.univ.image cells, (entry a' c : ℝ)) -
        (∑ p : Fin stages.length × Fin (6*(n+8)),
          physicalPairLineWeight cells (fun c => c.1 = r) p * μ p.1)| ≤
          (Nat.clog 2 (6*n) : ℝ) * (8*(X/6)) + 3*(X/6)/(n : ℝ) + 2*(X/6)) ∧
      (∀ c : Fin n, |(∑ z ∈ columnCells c, (entry a' z : ℝ)) -
        (∑ z ∈ columnCells c \ Finset.univ.image cells, (entry a' z : ℝ)) -
        (∑ p : Fin stages.length × Fin (6*(n+8)),
          physicalPairLineWeight cells (fun z => z.2 = c) p * μ p.1)| ≤
          (Nat.clog 2 (6*n) : ℝ) * (8*(X/6)) + 3*(X/6)/(n : ℝ) + 2*(X/6)) := by
  classical
  dsimp only
  let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
    offset hoff hs choice rows cols hr hc
  let μ := fun j => (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) /
    (6*(n+8) : ℕ)
  obtain ⟨T,U,V,ω,a',hsel,hmap,hperm,hfix,hstage,hgap,hbudget,hrow,hcol⟩ :=
    fw_growth_all_line_midpoint_witness trace hpool hn X hX hnarrow offset hoff hs choice rows cols hr hc
      reservedRows reservedCols hrows hcols a hplaced
  have hphysical := fw_growth_trace_midpoint_to_physical_lines trace hpool offset hoff hs choice rows cols hr hc
    a' ω hperm μ ((Nat.clog 2 (6*n) : ℝ) * (8*(X/6)) + 3*(X/6)/(n : ℝ) + 2*(X/6)) hrow hcol
  exact ⟨T,U,V,ω,a',hsel,hmap,hperm,hfix,hstage,hgap,hbudget,hrow,hcol,hphysical.1,hphysical.2⟩

end
end Sude
