import Sude.ScreenedPrefix
import Sude.BTGrowingPhysicalGrid

/-! Abstract FW seed grid extended by a supplied screened-prefix trace. -/
namespace Sude
noncomputable section

local instance : DecidableEq BTSelectedStage := Classical.decEq _

/-- Abstract seed labels are kept disjoint from actual trace-stage labels. -/
def fwSeedTraceGap : Sum (Fin 16) BTSelectedStage → ℕ
  | Sum.inl _ => 2
  | Sum.inr stage => stage.gap

def fwSeedTraceBase : Finset (Sum (Fin 16) BTSelectedStage) :=
  Finset.univ.image (Sum.inl : Fin 16 → Sum (Fin 16) BTSelectedStage)

def fwSeedTraceLabels (stages : List BTSelectedStage) : Finset (Sum (Fin 16) BTSelectedStage) :=
  fwSeedTraceBase ∪ (stages.map (Sum.inr : BTSelectedStage → Sum (Fin 16) BTSelectedStage)).toFinset

/-- Sixteen distinct abstract gap-two labels give the complete even grid
through 32. No physical seed pairs are constructed here. -/
theorem fw_sixteen_seed_even_grid : CompleteEvenGrid fwSeedTraceBase fwSeedTraceGap 32 := by
  intro t ht heven
  obtain ⟨z, hz⟩ := heven
  have hz16 : z ≤ 16 := by omega
  have hzcard : z ≤ (Finset.univ : Finset (Fin 16)).card := by simpa using hz16
  obtain ⟨chosen, hsub, hcard⟩ := Finset.exists_subset_card_eq hzcard
  refine ⟨chosen.image (Sum.inl : Fin 16 → Sum (Fin 16) BTSelectedStage), ?_, ?_⟩
  · exact Finset.image_subset_image hsub
  · rw [Finset.sum_image (by intro x hx y hy hxy; exact Sum.inl_injective hxy)]
    simp only [fwSeedTraceGap, Finset.sum_const, nsmul_eq_mul, hcard]
    simpa [Nat.mul_comm] using hz.symm

/-- Any sixteen supplied distinct labels whose gaps are all two give the
same initial grid. The caller must establish both label distinctness and
their actual gap identities. -/
theorem fw_sixteen_supplied_seed_even_grid {α : Type*} [DecidableEq α]
    (seed : Fin 16 → α) (gap : α → ℕ) (hinj : Function.Injective seed)
    (hgap : ∀ i, gap (seed i) = 2) :
    CompleteEvenGrid (Finset.univ.image seed) gap 32 := by
  intro t ht heven
  obtain ⟨z, hz⟩ := heven
  have hz16 : z ≤ 16 := by omega
  have hzcard : z ≤ (Finset.univ : Finset (Fin 16)).card := by simpa using hz16
  obtain ⟨chosen, hsub, hcard⟩ := Finset.exists_subset_card_eq hzcard
  refine ⟨chosen.image seed, Finset.image_subset_image hsub, ?_⟩
  rw [Finset.sum_image (by intro x hx y hy hxy; exact hinj hxy)]
  simp only [hgap, Finset.sum_const, nsmul_eq_mul, hcard]
  simpa [Nat.mul_comm] using hz.symm

/-- A supplied actual screened-pool growth trace starting at the 16-seed
radius extends the abstract even grid to its exact final radius. The trace,
its pool reservations and reaching `X/23` are explicit inputs; this theorem
does not construct the sixteen physical seed slots or claim feasibility of
any screened-prefix numeric or mixed-stage source recipe. -/
theorem fw_screened_seed_trace_bridge_grid (n : ℕ) (reserved final : Finset ℕ)
    (last : ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      ((poolFinset n).filter (fun p => 43 < p) \ reserved) 32 final last stages)
    (hcoverage : (poolMaximum n : ℝ) / 23 ≤ last) :
    CompleteEvenGrid (fwSeedTraceLabels stages) fwSeedTraceGap last ∧
      2 ∣ last ∧ (poolMaximum n : ℝ) / 23 ≤ last := by
  classical
  let labels : List (Sum (Fin 16) BTSelectedStage) := stages.map Sum.inr
  have hQ : 0 < 6 * (n + 8) := by omega
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
  refine ⟨?_, heven, hcoverage⟩
  change CompleteStepGrid (fwSeedTraceLabels stages) fwSeedTraceGap 2 last
  rw [hlast]
  rw [hsum] at hgrid
  simpa [fwSeedTraceLabels, labels] using hgrid

end
end Sude
