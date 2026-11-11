import Sude.BTGrowingTrace

/-! Relate traced variable gaps to actual physical pair labels. -/
namespace Sude
noncomputable section

/-- Replacing abstract traced stages by physical labels with the same gaps
preserves the growing step-grid chain. -/
theorem BTGrowingTrace.physical_step_chain {K : Type*} {g Q : ℕ}
    {unused final : Finset ℕ} {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q unused radius final last stages)
    (gap : K → ℕ) (labels : List K)
    (hlabels : List.Forall₂ (fun stage label => gap label = stage.gap) stages labels)
    (gridRadius : ℕ) (hstart : radius ≤ gridRadius) :
    StepGapChain gap g gridRadius labels := by
  induction trace generalizing labels gridRadius with
  | nil =>
    cases hlabels
    exact StepGapChain.nil _
  | cons unused radius stage final last tail hgap hdiv hbound hminimum hcard hmatch hsub hrest ih =>
    cases hlabels with
    | cons hlabel hlabels =>
      have hle : stage.gap ≤ gridRadius := hbound.trans hstart
      apply StepGapChain.cons gridRadius _ _ (by simpa [hlabel] using hdiv) (by omega)
      apply ih _ hlabels
      rw [hlabel]
      omega

/-- A real seed pair and physically labelled traced stage pairs realize all
multiples of `g` up to their actual accumulated gap total. The caller supplies
the actual pair labels and their verified gap identities. -/
theorem BTGrowingTrace.physical_seeded_step_grid {K : Type*} [DecidableEq K] {g Q : ℕ}
    {unused final : Finset ℕ} {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q unused radius final last stages)
    (gap : K → ℕ) (seed : K) (labels : List K)
    (hg : 0 < g) (hseed : gap seed = g) (hstart : radius ≤ g)
    (hnodup : labels.Nodup) (hfresh : seed ∉ labels)
    (hlabels : List.Forall₂ (fun stage label => gap label = stage.gap) stages labels) :
    CompleteStepGrid ({seed} ∪ labels.toFinset) gap g (g + (labels.map gap).sum) := by
  have hbase : CompleteStepGrid {seed} gap g g := by
    intro t ht hd
    obtain ⟨j, hj⟩ := hd
    have hjle : j ≤ 1 := by
      by_contra hn
      have hj2 : 2 ≤ j := by omega
      have hm := Nat.mul_le_mul_left g hj2
      nlinarith [hm]
    have hjcases : j = 0 ∨ j = 1 := by omega
    rcases hjcases with hj0 | hj1
    · subst j
      simp at hj
      subst t
      exact ⟨∅, by simp, by simp⟩
    · subst j
      simp at hj
      subst t
      exact ⟨{seed}, by simp, by simp [hseed]⟩
  apply extend_step_gap_chain gap g {seed} g labels hg hbase (dvd_refl g) hnodup
  · intro label hl
    simp only [Finset.mem_singleton]
    intro he
    subst label
    exact hfresh hl
  · exact trace.physical_step_chain gap labels hlabels g hstart

end
end Sude
