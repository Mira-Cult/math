import Sude.FWGrowthPermutedTraceMidpoints
import Sude.FWGrowthOrdinaryPhysicalDP

/-! The ordinary-slot deterministic allocator on the same trace-placed
square. Full-line centering, diagonals, and target construction are separate. -/
namespace Sude
noncomputable section
set_option maxHeartbeats 3000000

/-- Given an existing permuted trace placement, simultaneously rebalance its
ordinary slots and retain an explicit trace permutation for the resulting
square. The controlled quantity is the ordinary contribution centered at
the original ordinary-label means; all other line terms remain separate. -/
theorem fw_growth_ordinary_trace_dp {n L : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6*(n+8)) initial radius final last stages)
    (hpool : ∀ p ∈ initial, p ∈ pool n)
    (X : ℝ) (hX : 0 ≤ X) (hnarrow : NarrowedStages (X/6) stages)
    (ω₀ : Fin stages.length → Equiv.Perm (Fin (6*(n+8))))
    (offset : ℕ) (hoff : offset + stages.length*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = stages.length*3) (hc : cols.length = stages.length*3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows rows)
    (hcols : LayerPacking.PackedLayers reservedCols cols)
    (a : Cell n ≃ Fin (n*n))
    (hplaced : ∀ x, entry a (btGrowingOffsetPairCells (Q := 6*(n+8))
      (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc x) =
        (trace.poolValues rfl hpool (stagePairPermutation ω₀ x)).val) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    let population := fwGrowthOrdinaryPopulation n stages.length
    let midpoint := fun s : Fin stages.length × Fin (6*(n+8)) =>
      growthStageMidpoint (stages.get s.1) (trace.lowAt rfl s.1 (ω₀ s.1 s.2))
    let w := fun (l : Fin ((n+n)+2)) s =>
      physicalPairLineWeight cells (fun c => c ∈ physicalAllLineCells l) s
    ∃ (e : {s // s ∈ population} ≃ {s // s ∈ population})
      (ω : Fin stages.length → Equiv.Perm (Fin (6*(n+8))))
      (a' : Cell n ≃ Fin (n*n)),
      (∀ s, (e s).val.1 = s.val.1) ∧
      (∀ x, entry a' (cells x) = (trace.poolValues rfl hpool (stagePairPermutation ω x)).val) ∧
      (∀ s (hmem : s ∈ population) side,
        entry a' (cells (s,side)) = entry a (cells ((e ⟨s,hmem⟩).val,side))) ∧
      (∀ c, c ∉ Set.range (fun x : {s // s ∈ population} × Bool => cells (x.1.val,x.2)) →
        entry a' c = entry a c) ∧
      (∀ j i, i ∉ fwGrowthOrdinarySlots n → ∀ side,
        entry a' (cells ((j,i),side)) = entry a (cells ((j,i),side))) ∧
      (∀ j, Finset.univ.image (fun x : Fin (6*(n+8)) × Bool => entry a' (cells ((j,x.1),x.2))) =
        Finset.univ.image (fun x : Fin (6*(n+8)) × Bool => entry a (cells ((j,x.1),x.2)))) ∧
      (∀ j i, entry a' (cells ((j,i),true)) = entry a' (cells ((j,i),false)) + (stages.get j).gap) ∧
      (∀ l : Fin ((n+n)+2),
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
  obtain ⟨hcells, hgap₀, hmid₀⟩ := growth_permuted_trace_midpoints trace rfl hpool cells a ω₀ hplaced
  obtain ⟨e, a', he, hentry, hfix, hnon, hset, hgap, hbound⟩ :=
    fw_growth_ordinary_physical_dp trace X hX hnarrow ω₀ offset hoff hs choice rows cols hr hc
      reservedRows reservedCols hrows hcols a hcells (by simpa [BTStageTrace.stageAt, add_comm] using hmid₀)
  obtain ⟨ρ, hρin, hρout⟩ := prefix_stagewise_subset_permutation population e he
  let ω : Fin stages.length → Equiv.Perm (Fin (6*(n+8))) := fun j => (ρ j).trans (ω₀ j)
  refine ⟨e, ω, a', he, ?_, hentry, hfix, hnon, hset, ?_, hbound⟩
  · rintro ⟨⟨j,i⟩,side⟩
    by_cases hi : (j,i) ∈ population
    · have hρ := hρin j i hi
      rw [hentry (j,i) hi side, ← hρ, hplaced]
      rfl
    · have hi' : i ∉ fwGrowthOrdinarySlots n := by
        simpa [population, fwGrowthOrdinaryPopulation] using hi
      rw [hnon j i hi' side, hplaced]
      simp [ω, stagePairPermutation, hρout j i hi]
  · exact hgap (fun j => (stages.get j).gap) (by simpa [BTStageTrace.stageAt] using hgap₀)

end
end Sude
