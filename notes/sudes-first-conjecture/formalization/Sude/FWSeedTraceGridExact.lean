import Sude.FWSeedTraceGrid

namespace Sude
noncomputable section
local instance fwSeedTraceGridExactStageDecidable : DecidableEq BTSelectedStage := Classical.decEq _

/-- Sixteen abstract gap-two seed labels and an arbitrary supplied growing
trace extend the complete even grid to the exact final radius, without a
coverage assumption. This establishes no physical placement. -/
theorem fw_seed_trace_even_grid_unconditional_coverage {Q : ℕ}
    {initial final : Finset ℕ} {last : ℕ} {stages : List BTSelectedStage}
    (hQ : 0 < Q) (trace : BTGrowingTrace 2 Q initial 32 final last stages) :
    CompleteEvenGrid (fwSeedTraceLabels stages) fwSeedTraceGap last ∧ 2 ∣ last := by
  classical
  let labels : List (Sum (Fin 16) BTSelectedStage) := stages.map Sum.inr
  have hnodup : labels.Nodup := List.Nodup.map Sum.inr_injective (trace.nodup hQ)
  have hfresh : ∀ label ∈ labels, label ∉ fwSeedTraceBase := by
    intro label hl
    obtain ⟨stage, hs, rfl⟩ := List.mem_map.mp hl
    simp [fwSeedTraceBase]
  have hlabels : List.Forall₂ (fun stage label => fwSeedTraceGap label = stage.gap) stages labels := by
    have hall : ∀ ss : List BTSelectedStage,
        List.Forall₂ (fun stage label => fwSeedTraceGap label = stage.gap)
          ss (ss.map (Sum.inr : BTSelectedStage → Sum (Fin 16) BTSelectedStage)) := by
      intro ss
      induction ss with
      | nil => exact List.Forall₂.nil
      | cons stage tail ih => exact List.Forall₂.cons rfl ih
    exact hall stages
  have hchain := trace.physical_step_chain fwSeedTraceGap labels hlabels 32 (by rfl)
  have hbase : CompleteStepGrid fwSeedTraceBase fwSeedTraceGap 2 32 := fw_sixteen_seed_even_grid
  have hgrid := extend_step_gap_chain fwSeedTraceGap 2 fwSeedTraceBase 32 labels
    (by decide) hbase (by decide) hnodup hfresh hchain
  have hsum : (labels.map fwSeedTraceGap).sum = (stages.map BTSelectedStage.gap).sum := by
    simp [labels, List.map_map, Function.comp_def, fwSeedTraceGap]
  have hlast := trace.final_accounting.2.2
  have hevenSum : 2 ∣ (stages.map BTSelectedStage.gap).sum := by
    apply List.dvd_sum
    intro x hx
    obtain ⟨stage, hs, rfl⟩ := List.mem_map.mp hx
    exact (trace.stage_properties stage hs).2.1
  have heven : 2 ∣ last := by rw [hlast]; exact dvd_add (by decide) hevenSum
  refine ⟨?_, heven⟩
  change CompleteStepGrid (fwSeedTraceLabels stages) fwSeedTraceGap 2 last
  rw [hlast]
  rw [hsum] at hgrid
  simpa [fwSeedTraceLabels, labels] using hgrid

/-- Any sixteen distinct supplied seed labels with actual gap two, together
with a supplied trace, extend the abstract even grid through its exact final
radius. Tagged trace labels keep the two classes distinct. -/
theorem fw_supplied_seed_trace_even_grid {α : Type*} [DecidableEq α] {Q : ℕ}
    {initial final : Finset ℕ} {last : ℕ} {stages : List BTSelectedStage}
    (seed : Fin 16 → α) (seedGap : α → ℕ)
    (hinj : Function.Injective seed) (hgap : ∀ i, seedGap (seed i) = 2)
    (hQ : 0 < Q) (trace : BTGrowingTrace 2 Q initial 32 final last stages) :
    let gap : Sum α BTSelectedStage → ℕ := Sum.elim seedGap BTSelectedStage.gap
    let base := Finset.univ.image (fun i => Sum.inl (seed i) : Fin 16 → Sum α BTSelectedStage)
    let labels : List (Sum α BTSelectedStage) := stages.map Sum.inr
    CompleteEvenGrid (base ∪ labels.toFinset) gap last ∧ 2 ∣ last := by
  classical
  dsimp only
  let gap : Sum α BTSelectedStage → ℕ := Sum.elim seedGap BTSelectedStage.gap
  let slabel : Fin 16 → Sum α BTSelectedStage := fun i => Sum.inl (seed i)
  let labels : List (Sum α BTSelectedStage) := stages.map Sum.inr
  have hseedinj : Function.Injective slabel := Sum.inl_injective.comp hinj
  have hseedgap : ∀ i, gap (slabel i) = 2 := by intro i; exact hgap i
  have hbase : CompleteStepGrid (Finset.univ.image slabel) gap 2 32 :=
    fw_sixteen_supplied_seed_even_grid slabel gap hseedinj hseedgap
  have hnodup : labels.Nodup := List.Nodup.map Sum.inr_injective (trace.nodup hQ)
  have hfresh : ∀ label ∈ labels, label ∉ Finset.univ.image slabel := by
    intro label hl
    obtain ⟨stage, hs, rfl⟩ := List.mem_map.mp hl
    simp [slabel]
  have hlabels : List.Forall₂ (fun stage label => gap label = stage.gap) stages labels := by
    have hall : ∀ ss : List BTSelectedStage,
        List.Forall₂ (fun stage label => gap label = stage.gap)
          ss (ss.map (Sum.inr : BTSelectedStage → Sum α BTSelectedStage)) := by
      intro ss
      induction ss with
      | nil => exact List.Forall₂.nil
      | cons stage tail ih => exact List.Forall₂.cons rfl ih
    exact hall stages
  have hchain := trace.physical_step_chain gap labels hlabels 32 (by rfl)
  have hgrid := extend_step_gap_chain gap 2 (Finset.univ.image slabel) 32 labels
    (by decide) hbase (by decide) hnodup hfresh hchain
  have hsum : (labels.map gap).sum = (stages.map BTSelectedStage.gap).sum := by
    simp [labels, List.map_map, Function.comp_def, gap]
  have hlast := trace.final_accounting.2.2
  have hevenSum : 2 ∣ (stages.map BTSelectedStage.gap).sum := by
    apply List.dvd_sum
    intro x hx
    obtain ⟨stage, hs, rfl⟩ := List.mem_map.mp hx
    exact (trace.stage_properties stage hs).2.1
  have heven : 2 ∣ last := by rw [hlast]; exact dvd_add (by decide) hevenSum
  refine ⟨?_, heven⟩
  change CompleteStepGrid ((Finset.univ.image slabel) ∪ labels.toFinset) gap 2 last
  rw [hlast]
  rw [hsum] at hgrid
  exact hgrid


end
end Sude
