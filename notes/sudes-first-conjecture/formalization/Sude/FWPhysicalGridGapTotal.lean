import Sude.FWJointGridGapTotal
import Sude.FWJointSupportedGap
import Sude.FWPhysicalEdgeTraceGrid

/-! Connect a supplied physical edge's supported gaps to its trace radius.
The edge, slot map, gap identities and physical witness are explicit inputs. -/
namespace Sude
noncomputable section

/-- The physical trace radius equals the total of the supplied seed and
growth gaps, including the empty-growth case. -/
theorem fw_physical_trace_gap_total {n Q : ℕ} {initial final : Finset ℕ}
    {last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 Q initial 32 final last stages)
    (a : Cell n ≃ Fin (n * n))
    (seedCells : Fin 16 → Bool → Cell n)
    (growthCells : Fin stages.length → Bool → Cell n)
    (hseed : ∀ i, entry a (seedCells i true) = entry a (seedCells i false) + 2)
    (hgrowth : ∀ i, entry a (growthCells i true) = entry a (growthCells i false) +
      (BTStageTrace.stageAt stages rfl i).gap) :
    (∑ i, fwPhysicalEdgeTraceGap a seedCells growthCells (Sum.inl i)) +
      (∑ i, fwPhysicalEdgeTraceGap a seedCells growthCells (Sum.inr i)) = last := by
  have hs : (∑ i, fwPhysicalEdgeTraceGap a seedCells growthCells (Sum.inl i)) = 32 := by
    have h : ∀ i, fwPhysicalEdgeTraceGap a seedCells growthCells (Sum.inl i) = 2 := by
      intro i
      dsimp [fwPhysicalEdgeTraceGap]
      rw [hseed i]
      omega
    simp [h]
  have hg : ∀ i, fwPhysicalEdgeTraceGap a seedCells growthCells (Sum.inr i) =
      (BTStageTrace.stageAt stages rfl i).gap := by
    intro i
    dsimp [fwPhysicalEdgeTraceGap]
    rw [hgrowth i]
    omega
  have hsum : (∑ i, (BTStageTrace.stageAt stages rfl i).gap) =
      (stages.map BTSelectedStage.gap).sum := by
    rw [← List.sum_ofFn]
    change (List.ofFn (BTSelectedStage.gap ∘ stages.get)).sum = _
    rw [← List.map_ofFn, List.ofFn_get]
  rw [hs]
  simp_rw [hg]
  rw [hsum, trace.final_accounting.2.2]

/-- Transport the exact physical trace total, the bridge gaps and the wide
gaps to one injectively indexed slot family. The slot-gap identity is the
same form supplied by `fw_joint_supported_gap_eq`; no identity of a chosen
wide family with any other witness is assumed. -/
theorem fw_physical_joint_grid_actual_total {n Q J : ℕ}
    {initial final : Finset ℕ} {last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 Q initial 32 final last stages)
    (a : Cell n ≃ Fin (n * n))
    (seedCells : Fin 16 → Bool → Cell n)
    (growthCells : Fin stages.length → Bool → Cell n)
    (hseed : ∀ i, entry a (seedCells i true) = entry a (seedCells i false) + 2)
    (hgrowth : ∀ i, entry a (growthCells i true) = entry a (growthCells i false) +
      (BTStageTrace.stageAt stages rfl i).gap)
    (bridge : ℕ → ℕ) (wide : Fin J → ℕ) {K : Type*} [DecidableEq K]
    (slot : {x // x ∈ fwJointGridLabels (fwJointPreWideGridLabels stages.length) J} → K)
    (gap : K → ℕ) (hinj : Function.Injective slot)
    (hgap : ∀ x, gap (slot x) =
      Sum.elim (Sum.elim (fwPhysicalEdgeTraceGap a seedCells growthCells) bridge) wide x.val) :
    (∑ k ∈ (fwJointGridLabels (fwJointPreWideGridLabels stages.length) J).attach.image slot, gap k) =
      last + (∑ i ∈ Finset.range 5, bridge i) + ∑ i, wide i := by
  let seed := fun i => fwPhysicalEdgeTraceGap a seedCells growthCells (Sum.inl i)
  let growth := fun i => fwPhysicalEdgeTraceGap a seedCells growthCells (Sum.inr i)
  have hg : ∀ x, gap (slot x) =
      Sum.elim (Sum.elim (Sum.elim seed growth) bridge) wide x.val := by
    intro x
    have h := hgap x
    rcases x with ⟨(((i | i) | i) | i), hi⟩ <;>
      simpa [seed, growth, fwPhysicalEdgeTraceGap] using h
  rw [fw_joint_grid_gap_total_on_slots seed growth bridge wide slot gap hinj hg]
  rw [fw_physical_trace_gap_total trace a seedCells growthCells hseed hgrowth]

end
end Sude
