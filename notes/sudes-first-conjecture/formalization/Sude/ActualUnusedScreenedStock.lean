import Sude.ActualUnusedPool
import Sude.ScreenedPool
import Sude.BTGrowingUnscreenedStock

/-! Actual unused-pool bookkeeping for a supplied square and supplied role
value image. No keepout-complement equality or seed availability is asserted. -/
namespace Sude
noncomputable section
local instance actualUnusedScreenedStockDecidableEqStage : DecidableEq BTSelectedStage := Classical.decEq _

/-- Forgetting the subtype from the actual unused pool gives precisely the
full prescribed pool with the reserved cells' actual values removed. -/
theorem actualUnusedPool_value_image_eq {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (roles : Finset (Cell n)) :
    (actualUnusedPool a roles).image Subtype.val = poolFinset n \ roles.image (entry a) := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    apply Finset.mem_sdiff.mpr
    constructor
    · exact mem_poolFinset.mpr w.property
    · intro hv
      obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hv
      exact (mem_actualUnusedPool a roles w).mp hw z hz he.symm
  · intro hv
    obtain ⟨hp, hnot⟩ := Finset.mem_sdiff.mp hv
    let w : pool n := ⟨v, mem_poolFinset.mp hp⟩
    refine Finset.mem_image.mpr ⟨w, ?_, rfl⟩
    apply (mem_actualUnusedPool a roles w).mpr
    intro z hz he
    apply hnot
    exact Finset.mem_image.mpr ⟨z, hz, he.symm⟩

/-- If the actual role values are the supplied early values and the trace
footprints, the actual unused values are the final screened stock plus those
low pool values not already used early. The two pieces are disjoint. -/
theorem actualUnusedPool_value_image_eq_screened_stock
    {n g Q : ℕ} (a : Cell n ≃ Fin (n * n)) (roles : Finset (Cell n))
    (early : Finset ℕ) {final : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q (((poolFinset n).filter (fun x => 43 < x)) \ early)
      radius final last stages)
    (hroles : roles.image (entry a) = early ∪ stages.toFinset.biUnion BTSelectedStage.footprint) :
    (actualUnusedPool a roles).image Subtype.val =
      final ∪ (((poolFinset n).filter (fun x => x ≤ 43)) \ early) ∧
    Disjoint final (((poolFinset n).filter (fun x => x ≤ 43)) \ early) := by
  rw [actualUnusedPool_value_image_eq]
  exact trace.unscreened_complement_decomposition (poolFinset n) early (roles.image (entry a)) hroles

/-- The same statement when growth footprints are presented with a finite
stage index, as in the physical role-value coverage interface. -/
theorem actualUnusedPool_value_image_eq_screened_stock_indexed
    {n g Q P : ℕ} (a : Cell n ≃ Fin (n * n)) (roles : Finset (Cell n))
    (early : Finset ℕ) {final : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage} (hlen : stages.length = P)
    (trace : BTGrowingTrace g Q (((poolFinset n).filter (fun x => 43 < x)) \ early)
      radius final last stages)
    (hroles : roles.image (entry a) = early ∪ Finset.univ.biUnion
      (fun i : Fin P => (BTStageTrace.stageAt stages hlen i).footprint)) :
    (actualUnusedPool a roles).image Subtype.val =
      final ∪ (((poolFinset n).filter (fun x => x ≤ 43)) \ early) ∧
    Disjoint final (((poolFinset n).filter (fun x => x ≤ 43)) \ early) := by
  apply actualUnusedPool_value_image_eq_screened_stock a roles early trace
  rw [bt_stage_footprint_union_indexed stages hlen]
  exact hroles

end
end Sude
