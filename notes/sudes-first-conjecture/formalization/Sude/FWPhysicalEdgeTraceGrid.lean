import Sude.FWSeedTraceGrid

/-! Extend a physical seed-pair grid by the actual gaps of a supplied trace.
No distinctness of the supplied cells is assumed or concluded. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- The gap is measured from the two square entries named by each label. -/
def fwPhysicalEdgeTraceGap {n P : ℕ} (a : Cell n ≃ Fin (n * n))
    (seedCells : Fin 16 → Bool → Cell n) (growthCells : Fin P → Bool → Cell n) :
    Sum (Fin 16) (Fin P) → ℕ
  | Sum.inl i => entry a (seedCells i true) - entry a (seedCells i false)
  | Sum.inr i => entry a (growthCells i true) - entry a (growthCells i false)

/-- The sixteen supplied physical seed gaps and all physical trace gaps form
an even grid through the exact trace radius. Tags distinguish labels only;
no injectivity or disjointness of physical cells is asserted. -/
theorem fw_physical_edge_trace_grid {n Q : ℕ}
    (a : Cell n ≃ Fin (n * n))
    {initial final : Finset ℕ} {last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 Q initial 32 final last stages)
    (seedCells : Fin 16 → Bool → Cell n)
    (growthCells : Fin stages.length → Bool → Cell n)
    (hseed : ∀ i, entry a (seedCells i true) = entry a (seedCells i false) + 2)
    (hgrowth : ∀ i, entry a (growthCells i true) = entry a (growthCells i false) +
      (BTStageTrace.stageAt stages rfl i).gap) :
    CompleteEvenGrid (Finset.univ : Finset (Sum (Fin 16) (Fin stages.length)))
      (fwPhysicalEdgeTraceGap a seedCells growthCells) last ∧ 2 ∣ last := by
  classical
  let gap := fwPhysicalEdgeTraceGap a seedCells growthCells
  let seed : Fin 16 → Sum (Fin 16) (Fin stages.length) := Sum.inl
  let labels : List (Sum (Fin 16) (Fin stages.length)) := List.ofFn (fun j => Sum.inr j)
  have hseedgap : ∀ i, gap (seed i) = 2 := by
    intro i
    dsimp [gap, seed, fwPhysicalEdgeTraceGap]
    rw [hseed i]
    omega
  have hbase : CompleteStepGrid (Finset.univ.image seed) gap 2 32 :=
    fw_sixteen_supplied_seed_even_grid seed gap Sum.inl_injective hseedgap
  have hnodup : labels.Nodup := by
    apply List.nodup_ofFn.mpr
    intro i j hij
    exact Sum.inr_injective hij
  have hfresh : ∀ label ∈ labels, label ∉ Finset.univ.image seed := by
    intro label hl
    obtain ⟨i, _, rfl⟩ := List.mem_ofFn.mp hl
    simp [seed]
  have hlabels : List.Forall₂ (fun stage label => gap label = stage.gap) stages labels := by
    apply List.forall₂_of_length_eq_of_get
    · simp [labels]
    · intro i hi hj
      have hg := hgrowth ⟨i, hi⟩
      simp [labels, gap, fwPhysicalEdgeTraceGap, BTStageTrace.stageAt] at *
      omega
  have hchain := trace.physical_step_chain gap labels hlabels 32 (by rfl)
  have hgrid := extend_step_gap_chain gap 2 (Finset.univ.image seed) 32 labels
    (by decide) hbase (by decide) hnodup hfresh hchain
  have hsum : (labels.map gap).sum = (stages.map BTSelectedStage.gap).sum := by
    have hlist : labels.map gap = stages.map BTSelectedStage.gap := by
      apply List.ext_get
      · simp [labels]
      · intro i hi hj
        have hi' : i < stages.length := by simpa [labels] using hi
        have hg := hgrowth ⟨i, hi'⟩
        simp [labels, gap, fwPhysicalEdgeTraceGap, BTStageTrace.stageAt] at *
        omega
    rw [hlist]
  have hlast := trace.final_accounting.2.2
  have hevenSum : 2 ∣ (stages.map BTSelectedStage.gap).sum := by
    apply List.dvd_sum
    intro x hx
    obtain ⟨stage, hs, rfl⟩ := List.mem_map.mp hx
    exact (trace.stage_properties stage hs).2.1
  have heven : 2 ∣ last := by rw [hlast]; exact dvd_add (by decide) hevenSum
  refine ⟨?_, heven⟩
  change CompleteStepGrid Finset.univ gap 2 last
  rw [hlast]
  rw [hsum] at hgrid
  have huniv : (Finset.univ.image seed) ∪ labels.toFinset = Finset.univ := by
    ext x
    cases x <;> simp [seed, labels]
  rwa [huniv] at hgrid

end
end Sude
