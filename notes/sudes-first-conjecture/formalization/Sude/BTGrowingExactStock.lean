import Sude.BTGrowingTrace
import Sude.BTTracePoolValues

/-! Exact set bookkeeping for the supplied growing trace. No primality,
complete pool, or completion conclusion is asserted. -/
namespace Sude
noncomputable section
local instance btGrowingExactStockDecidableEqStage : DecidableEq BTSelectedStage := Classical.decEq _

/-- The trace removes exactly the union of its recorded stage footprints.
No positivity of the stage count or pair quota is required. -/
theorem BTGrowingTrace.final_eq_initial_sdiff_footprints
    {g Q : ℕ} {initial final : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial radius final last stages) :
    final = initial \ stages.toFinset.biUnion BTSelectedStage.footprint := by
  classical
  induction trace with
  | nil => simp
  | cons unused radius stage final last tail hgap hdiv hbound hminimum hcard hmatch hsub hrest ih =>
    rw [ih]
    ext x
    simp only [List.toFinset_cons, Finset.biUnion_insert, Finset.mem_sdiff, Finset.mem_union]
    tauto

/-- Enumerating the stage list by any exact finite index has the same union
of footprints, including when the index type is empty. -/
theorem bt_stage_footprint_union_indexed (stages : List BTSelectedStage)
    {P : ℕ} (hlen : stages.length = P) :
    stages.toFinset.biUnion BTSelectedStage.footprint =
      Finset.univ.biUnion (fun i : Fin P => (BTStageTrace.stageAt stages hlen i).footprint) := by
  classical
  ext x
  simp only [Finset.mem_biUnion, List.mem_toFinset, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨stage, hstage, hx⟩
    obtain ⟨i, hi⟩ := List.get_of_mem hstage
    refine ⟨Fin.cast hlen i, ?_⟩
    have hget : BTStageTrace.stageAt stages hlen (Fin.cast hlen i) = stage := by
      simpa [BTStageTrace.stageAt] using hi
    simpa [hget] using hx
  · rintro ⟨i, hx⟩
    exact ⟨BTStageTrace.stageAt stages hlen i, BTStageTrace.stageAt_mem stages hlen i, hx⟩

/-- The same exact stock identity with an explicitly indexed stage family. -/
theorem BTGrowingTrace.final_eq_initial_sdiff_indexed_footprints
    {g Q : ℕ} {initial final : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial radius final last stages)
    {P : ℕ} (hlen : stages.length = P) :
    final = initial \ Finset.univ.biUnion
      (fun i : Fin P => (BTStageTrace.stageAt stages hlen i).footprint) := by
  rw [trace.final_eq_initial_sdiff_footprints, bt_stage_footprint_union_indexed stages hlen]

end
end Sude
