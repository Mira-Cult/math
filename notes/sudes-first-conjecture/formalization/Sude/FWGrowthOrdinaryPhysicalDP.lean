import Sude.FWGrowthOrdinaryDPAllocation
import Sude.FWGrowthOrdinaryLineMass
import Sude.PrefixStagewisePhysicalPermutation

/-! Simultaneous deterministic ordinary-slot allocation on the same supplied
growth-square placement. Recentring and other line components are separate. -/
namespace Sude
noncomputable section
set_option maxHeartbeats 2000000

/-- On a current square whose growth-pair midpoints are indexed by the prior
stage permutation, simultaneously reallocate the ordinary pairs to control
all physical line contributions against the remaining-ordinary means. The
same resulting square fixes every cell outside the ordinary pair image,
preserves each stage's endpoint set, and preserves any stagewise common gaps.
All packing, injection, and current midpoint-placement facts are explicit. -/
theorem fw_growth_ordinary_physical_dp {n L : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6*(n+8)) initial radius final last stages)
    (X : ℝ) (hX : 0 ≤ X) (hnarrow : NarrowedStages (X/6) stages)
    (ω₀ : Fin stages.length → Equiv.Perm (Fin (6*(n+8))))
    (offset : ℕ) (hoff : offset + stages.length*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = stages.length*3) (hc : cols.length = stages.length*3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows rows)
    (hcols : LayerPacking.PackedLayers reservedCols cols)
    (a : Cell n ≃ Fin (n*n))
    (hcells : Function.Injective (btGrowingOffsetPairCells (Q := 6*(n+8))
      (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc))
    (hmid : ∀ j i,
      (((entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
          offset hoff hs choice rows cols hr hc ((j,i),true)) : ℝ) +
        entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
          offset hoff hs choice rows cols hr hc ((j,i),false))) / 2) =
        growthStageMidpoint (stages.get j) (trace.lowAt rfl j (ω₀ j i))) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    let population := fwGrowthOrdinaryPopulation n stages.length
    let midpoint := fun s : Fin stages.length × Fin (6*(n+8)) =>
      growthStageMidpoint (stages.get s.1) (trace.lowAt rfl s.1 (ω₀ s.1 s.2))
    let w := fun (l : Fin ((n+n)+2)) s =>
      physicalPairLineWeight cells (fun c => c ∈ physicalAllLineCells l) s
    ∃ (e : {s // s ∈ population} ≃ {s // s ∈ population})
      (a' : Cell n ≃ Fin (n*n)),
      (∀ s, (e s).val.1 = s.val.1) ∧
      (∀ s (hmem : s ∈ population) side,
        entry a' (cells (s,side)) = entry a (cells ((e ⟨s,hmem⟩).val,side))) ∧
      (∀ c, c ∉ Set.range (fun x : {s // s ∈ population} × Bool => cells (x.1.val,x.2)) →
        entry a' c = entry a c) ∧
      (∀ j i, i ∉ fwGrowthOrdinarySlots n → ∀ side,
        entry a' (cells ((j,i),side)) = entry a (cells ((j,i),side))) ∧
      (∀ j, Finset.univ.image (fun x : Fin (6*(n+8)) × Bool => entry a' (cells ((j,x.1),x.2))) =
        Finset.univ.image (fun x : Fin (6*(n+8)) × Bool => entry a (cells ((j,x.1),x.2)))) ∧
      (∀ gap : Fin stages.length → ℕ,
        (∀ j i, entry a (cells ((j,i),true)) = entry a (cells ((j,i),false)) + gap j) →
        ∀ j i, entry a' (cells ((j,i),true)) = entry a' (cells ((j,i),false)) + gap j) ∧
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
  let midpoint : (Fin stages.length × Fin (6*(n+8))) → ℝ := fun s =>
    growthStageMidpoint (stages.get s.1) (trace.lowAt rfl s.1 (ω₀ s.1 s.2))
  let w : Fin ((n+n)+2) → (Fin stages.length × Fin (6*(n+8))) → ℝ := fun l s =>
    physicalPairLineWeight cells (fun c => c ∈ physicalAllLineCells l) s
  have hw : ∀ l ∈ (Finset.univ : Finset (Fin ((n+n)+2))), ∀ s ∈ population, 0 ≤ w l s := by
    intro l _ s _
    exact physical_pair_all_line_weight_nonneg cells s l
  have hweight : ∀ s ∈ population, (∑ l : Fin ((n+n)+2), w l s) ≤ 4 := by
    rintro ⟨j,i⟩ hi
    have hi' : i ∈ fwGrowthOrdinarySlots n := by
      simpa [population, fwGrowthOrdinaryPopulation] using hi
    have hm := fw_growth_ordinary_all_line_mass offset hoff hs choice rows cols hr hc
      reservedRows reservedCols hrows hcols j i hi'
    exact le_of_eq hm
  obtain ⟨e, hstage, hbound⟩ := fw_growth_ordinary_dp_assignment trace X hX hnarrow ω₀
    Finset.univ w hw (by simpa using hweight)
  obtain ⟨a', hentry, hfix, hset, hgap⟩ :=
    prefix_reallocate_stagewise_subset a cells hcells population e hstage
  have hnonordinary : ∀ j i, i ∉ fwGrowthOrdinarySlots n → ∀ side,
      entry a' (cells ((j,i),side)) = entry a (cells ((j,i),side)) := by
    intro j i hi side
    apply hfix
    rintro ⟨⟨s,b⟩, he⟩
    have heq := hcells he
    have hs : s.val = (j,i) := congrArg Prod.fst heq
    have hin : s.val ∈ population := s.property
    rw [hs] at hin
    exact hi (by simpa [population, fwGrowthOrdinaryPopulation] using hin)
  refine ⟨e, a', hstage, hentry, hfix, hnonordinary, hset, hgap, ?_⟩
  intro l
  have hterm : ∀ s : {s // s ∈ population},
      (((entry a' (cells (s.val,true)) : ℝ) + entry a' (cells (s.val,false))) / 2) = midpoint (e s).val := by
    intro s
    rw [hentry s.val s.property true, hentry s.val s.property false]
    exact hmid (e s).val.1 (e s).val.2
  have hb := hbound l (Finset.mem_univ l)
  convert hb using 1
  congr 2
  apply Finset.sum_congr rfl
  intro s _
  rw [hterm s]

end
end Sude
