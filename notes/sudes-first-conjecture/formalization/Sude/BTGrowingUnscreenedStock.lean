import Sude.BTGrowingExactStock

/-! Exact bookkeeping for a supplied full set whose initial growth stock is
screened above 43. No seed availability or keepout-complement equality is
asserted. -/
namespace Sude
noncomputable section
local instance btGrowingUnscreenedStockDecidableEqStage : DecidableEq BTSelectedStage := Classical.decEq _

/-- If the supplied active values are exactly the early values together with
the recorded stage footprints, the full-set complement consists of the final
screened stock and the low values that were not early values. These two sets
are disjoint; early values may contain any number of low values. -/
theorem BTGrowingTrace.unscreened_complement_decomposition
    {g Q : ℕ} (U early active : Finset ℕ) {final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q ((U.filter (fun x => 43 < x)) \ early)
      radius final last stages)
    (hactive : active = early ∪ stages.toFinset.biUnion BTSelectedStage.footprint) :
    U \ active = final ∪ ((U.filter (fun x => x ≤ 43)) \ early) ∧
    Disjoint final ((U.filter (fun x => x ≤ 43)) \ early) := by
  classical
  let growth := stages.toFinset.biUnion BTSelectedStage.footprint
  have hgrowth : growth ⊆ (U.filter (fun x => 43 < x)) \ early := by
    intro x hx
    obtain ⟨stage, hstage, hx⟩ := Finset.mem_biUnion.mp hx
    exact trace.footprints_subset stage (List.mem_toFinset.mp hstage) hx
  have hfinal : final ⊆ (U.filter (fun x => 43 < x)) \ early :=
    trace.final_accounting.1
  have hdeletion : final = ((U.filter (fun x => 43 < x)) \ early) \ growth :=
    trace.final_eq_initial_sdiff_footprints
  change active = early ∪ growth at hactive
  constructor
  · rw [hactive, hdeletion]
    ext x
    have hxgrowth : x ∈ growth → 43 < x := by
      intro hx
      exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hgrowth hx)).1).2
    by_cases hsmall : x ≤ 43
    · have hnotGrowth : x ∉ growth := by
        intro hx
        have hxgt := hxgrowth hx
        omega
      have hnotLarge : ¬ 43 < x := by omega
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter]
      tauto
    · have hlarge : 43 < x := by omega
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter]
      tauto
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    have hgt := (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hfinal hx)).1).2
    have hle := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hy).1).2
    omega

end
end Sude
