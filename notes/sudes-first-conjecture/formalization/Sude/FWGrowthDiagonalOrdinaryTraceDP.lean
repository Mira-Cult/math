import Sude.FWGrowthDiagonalAllocation
import Sude.FWGrowthOrdinaryTraceDP

/-! One same-square composition of the preselected diagonal/partner families
and the subsequent deterministic ordinary-slot allocation. This does not
recenter the ordinary reference or bound a complete line. -/
namespace Sude
noncomputable section
set_option maxHeartbeats 5000000

/-- Preserve the selected diagonal and partner families while simultaneously
balancing ordinary midpoint contributions on the resulting trace-placed square.
The first permutation records the selected source labels; the second records
the final trace placement. Nonordinary pair entries are identical on both
squares. -/
theorem fw_growth_diagonal_ordinary_trace_dp {n L : ℕ} {initial final : Finset ℕ}
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
    let population := fwGrowthOrdinaryPopulation n stages.length
    let w := fun (l : Fin ((n+n)+2)) s =>
      physicalPairLineWeight cells (fun c => c ∈ physicalAllLineCells l) s
    ∃ (T U V : Fin stages.length → Finset ℕ)
      (ω₀ ω : Fin stages.length → Equiv.Perm (Fin (6*(n+8))))
      (a₀ a' : Cell n ≃ Fin (n*n))
      (e : {s // s ∈ population} ≃ {s // s ∈ population}),
      (∀ j, T j ⊆ (stages.get j).lows ∧ U j ⊆ (stages.get j).lows \ T j ∧
        V j ⊆ (stages.get j).lows \ (T j ∪ U j) ∧
        (T j).card = 12 ∧ (U j).card = 12 ∧ (V j).card = 24) ∧
      (∀ j, (fwGrowthMainSlots n).image (fun i => trace.lowAt rfl j (ω₀ j i)) = T j ∧
        (fwGrowthAntiSlots n).image (fun i => trace.lowAt rfl j (ω₀ j i)) = U j ∧
        (fwGrowthPartnerSlots n).image (fun i => trace.lowAt rfl j (ω₀ j i)) = V j) ∧
      (∀ x, entry a₀ (cells x) = (trace.poolValues rfl hpool (stagePairPermutation ω₀ x)).val) ∧
      (∀ x, entry a' (cells x) = (trace.poolValues rfl hpool (stagePairPermutation ω x)).val) ∧
      (∀ s, (e s).val.1 = s.val.1) ∧
      (∀ s (hmem : s ∈ population) side,
        entry a' (cells (s,side)) = entry a₀ (cells ((e ⟨s,hmem⟩).val,side))) ∧
      (∀ c, c ∉ Set.range (fun x : {s // s ∈ population} × Bool => cells (x.1.val,x.2)) →
        entry a' c = entry a₀ c) ∧
      (∀ j i, i ∉ fwGrowthOrdinarySlots n → ∀ side,
        entry a' (cells ((j,i),side)) = entry a₀ (cells ((j,i),side))) ∧
      (∀ j i, i ∉ fwGrowthOrdinarySlots n → ω j i = ω₀ j i) ∧
      (∀ j, (fwGrowthMainSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = T j ∧
        (fwGrowthAntiSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = U j ∧
        (fwGrowthPartnerSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = V j) ∧
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
        |(∑ s : {s // s ∈ population}, w l s.val *
            (((entry a' (cells (s.val,true)) : ℝ) + entry a' (cells (s.val,false))) / 2)) -
          ∑ j ∈ population.image Prod.fst,
            (∑ s ∈ population.filter (fun s => s.1 = j), w l s) *
              prefixOriginalStageMean population Prod.fst midpoint j| ≤
          (Nat.clog 2 (6*n) : ℝ) * (8 * (X/6))) := by
  classical
  dsimp only
  let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
    offset hoff hs choice rows cols hr hc
  let population := fwGrowthOrdinaryPopulation n stages.length
  obtain ⟨T, U, V, ω₀, a₀, hsel, hmap, hperm₀, hfix₀, hstage₀, hgap₀, hbudget⟩ :=
    fw_growth_three_family_allocation trace hpool hn X hX hnarrow offset hoff hs choice rows cols hr hc a hplaced
  obtain ⟨e, ω, a', he, hperm, hentry, hfix, hnon, hstage, hgap, hbound⟩ :=
    fw_growth_ordinary_trace_dp trace hpool X hX hnarrow ω₀ offset hoff hs choice rows cols hr hc
      reservedRows reservedCols hrows hcols a₀ hperm₀
  have hωsame : ∀ j i, i ∉ fwGrowthOrdinarySlots n → ω j i = ω₀ j i := by
    intro j i hi
    have hv : (trace.poolValues rfl hpool ((j,ω j i),false)).val =
        (trace.poolValues rfl hpool ((j,ω₀ j i),false)).val := by
      calc
        _ = entry a' (cells ((j,i),false)) := by simpa [stagePairPermutation] using (hperm ((j,i),false)).symm
        _ = entry a₀ (cells ((j,i),false)) := hnon j i hi false
        _ = _ := by simpa [stagePairPermutation] using hperm₀ ((j,i),false)
    have hi' := trace.poolValues_injective rfl hpool (Subtype.ext hv)
    exact congrArg (fun x => x.1.2) hi'
  have hmapfinal : ∀ j, (fwGrowthMainSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = T j ∧
        (fwGrowthAntiSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = U j ∧
        (fwGrowthPartnerSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = V j := by
    intro j
    have hd := (fw_growth_slot_groups_disjoint n).2.2.2
    have hnmain : ∀ i ∈ fwGrowthMainSlots n, i ∉ fwGrowthOrdinarySlots n := by
      intro i hi ho
      exact (Finset.disjoint_left.mp hd) ho (Finset.mem_union_left _ (Finset.mem_union_left _ hi))
    have hnanti : ∀ i ∈ fwGrowthAntiSlots n, i ∉ fwGrowthOrdinarySlots n := by
      intro i hi ho
      exact (Finset.disjoint_left.mp hd) ho (Finset.mem_union_left _ (Finset.mem_union_right _ hi))
    have hnpartner : ∀ i ∈ fwGrowthPartnerSlots n, i ∉ fwGrowthOrdinarySlots n := by
      intro i hi ho
      exact (Finset.disjoint_left.mp hd) ho (Finset.mem_union_right _ hi)
    refine ⟨?_, ?_, ?_⟩
    · calc
        _ = (fwGrowthMainSlots n).image (fun i => trace.lowAt rfl j (ω₀ j i)) := by
          apply Finset.image_congr
          intro i hi
          change trace.lowAt rfl j (ω j i) = trace.lowAt rfl j (ω₀ j i)
          rw [hωsame j i (hnmain i hi)]
        _ = T j := (hmap j).1
    · calc
        _ = (fwGrowthAntiSlots n).image (fun i => trace.lowAt rfl j (ω₀ j i)) := by
          apply Finset.image_congr
          intro i hi
          change trace.lowAt rfl j (ω j i) = trace.lowAt rfl j (ω₀ j i)
          rw [hωsame j i (hnanti i hi)]
        _ = U j := (hmap j).2.1
    · calc
        _ = (fwGrowthPartnerSlots n).image (fun i => trace.lowAt rfl j (ω₀ j i)) := by
          apply Finset.image_congr
          intro i hi
          change trace.lowAt rfl j (ω j i) = trace.lowAt rfl j (ω₀ j i)
          rw [hωsame j i (hnpartner i hi)]
        _ = V j := (hmap j).2.2
  have hfixall : ∀ c, c ∉ Set.range cells → entry a' c = entry a c := by
    intro c hc
    have hca : c ∉ Set.range (fun x : {s // s ∈ population} × Bool => cells (x.1.val,x.2)) := by
      rintro ⟨x, hx⟩
      exact hc ⟨(x.1.val,x.2), hx⟩
    exact (hfix c hca).trans (hfix₀ c hc)
  have hstageall : ∀ j, Finset.univ.image (fun x : Fin (6*(n+8)) × Bool => entry a' (cells ((j,x.1),x.2))) =
      Finset.univ.image (fun x : Fin (6*(n+8)) × Bool => entry a (cells ((j,x.1),x.2))) := by
    intro j
    exact (hstage j).trans (hstage₀ j)
  exact ⟨T, U, V, ω₀, ω, a₀, a', e, hsel, hmap, hperm₀, hperm, he, hentry, hfix,
    hnon, hωsame, hmapfinal, hfixall, hstageall, hgap, hbudget, hbound⟩

end
end Sude
