import Sude.BTTraceStepGrid

/-! The source controller grows its grid radius by each selected gap. -/
namespace Sude
noncomputable section
local instance : DecidableEq BTSelectedStage := Classical.decEq _

/-- Actual disjoint prime-pair selections, with the source update
`radius ↦ radius + gap`. The earlier `BTStageTrace` is a useful restricted
variant, but does not represent the controller's growth recurrence. -/
inductive BTGrowingTrace (g Q : ℕ) : Finset ℕ → ℕ → Finset ℕ → ℕ → List BTSelectedStage → Prop
  | nil (unused : Finset ℕ) (radius : ℕ) : BTGrowingTrace g Q unused radius unused radius []
  | cons (unused : Finset ℕ) (radius : ℕ) (stage : BTSelectedStage)
      (final : Finset ℕ) (lastRadius : ℕ) (tail : List BTSelectedStage)
      (hgap : 0 < stage.gap) (hdiv : g ∣ stage.gap)
      (hbound : stage.gap ≤ radius) (hminimum : stage.minimum ≤ stage.gap)
      (hcard : stage.lows.card = Q) (hmatch : PairwiseDisjointPairs stage.lows stage.gap)
      (hsub : stage.footprint ⊆ unused)
      (hrest : BTGrowingTrace g Q (unused \ stage.footprint) (radius + stage.gap) final lastRadius tail) :
      BTGrowingTrace g Q unused radius final lastRadius (stage :: tail)

theorem BTGrowingTrace.footprints_subset {g Q : ℕ} {unused final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (h : BTGrowingTrace g Q unused radius final last stages) :
    ∀ stage ∈ stages, stage.footprint ⊆ unused := by
  induction h with
  | nil => simp
  | cons unused radius stage final last tail hgap hdiv hbound hminimum hcard hmatch hsub hrest ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hsub
    · exact (ih s hs).trans Finset.sdiff_subset

theorem BTGrowingTrace.stage_properties {g Q : ℕ} {unused final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (h : BTGrowingTrace g Q unused radius final last stages) :
    ∀ stage ∈ stages, 0 < stage.gap ∧ g ∣ stage.gap ∧ stage.minimum ≤ stage.gap ∧
      stage.lows.card = Q ∧ PairwiseDisjointPairs stage.lows stage.gap := by
  induction h with
  | nil => simp
  | cons unused radius stage final last tail hgap hdiv hbound hminimum hcard hmatch hsub hrest ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨hgap, hdiv, hminimum, hcard, hmatch⟩
    · exact ih s hs

theorem BTGrowingTrace.pairwise_disjoint {g Q : ℕ} {unused final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (h : BTGrowingTrace g Q unused radius final last stages) :
    stages.Pairwise (fun x y => Disjoint x.footprint y.footprint) := by
  induction h with
  | nil => exact List.Pairwise.nil
  | cons unused radius stage final last tail hgap hdiv hbound hminimum hcard hmatch hsub hrest ih =>
    apply List.Pairwise.cons
    · intro s hs
      have htail := hrest.footprints_subset s hs
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      exact (Finset.mem_sdiff.mp (htail hz')).2 hz
    · exact ih

theorem BTGrowingTrace.final_accounting {g Q : ℕ} {unused final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (h : BTGrowingTrace g Q unused radius final last stages) :
    final ⊆ unused ∧ final.card + 2 * Q * stages.length = unused.card ∧
      last = radius + (stages.map BTSelectedStage.gap).sum := by
  induction h with
  | nil => simp
  | cons unused radius stage final last tail hgap hdiv hbound hminimum hcard hmatch hsub hrest ih =>
    have hfoot : stage.footprint.card = 2 * Q := by
      rw [BTSelectedStage.footprint, pairFootprint_card stage.lows stage.gap hgap hmatch, hcard]
    have hc := Finset.card_sdiff_add_card_eq_card hsub
    rw [hfoot] at hc
    refine ⟨ih.1.trans Finset.sdiff_subset, ?_, ?_⟩
    · simp only [List.length_cons, Nat.mul_succ]
      omega
    · simpa [List.map_cons, List.sum_cons, add_assoc, add_comm, add_left_comm] using ih.2.2

theorem BTGrowingTrace.nodup {g Q : ℕ} {unused final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q unused radius final last stages) (hQ : 0 < Q) : stages.Nodup := by
  induction trace with
  | nil => simp
  | cons unused radius stage final last tail hgap hdiv hbound hminimum hcard hmatch hsub hrest ih =>
    apply List.nodup_cons.mpr
    constructor
    · intro hmem
      have hp : 0 < stage.lows.card := by omega
      obtain ⟨p, hp⟩ := Finset.card_pos.mp hp
      have hfoot : p ∈ stage.footprint := Finset.mem_union_left _ hp
      have htail := hrest.footprints_subset stage hmem
      exact (Finset.mem_sdiff.mp (htail hfoot)).2 hfoot
    · exact ih

theorem BTGrowingTrace.step_gap_chain {g Q : ℕ} {unused final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q unused radius final last stages) :
    StepGapChain BTSelectedStage.gap g radius stages := by
  induction trace with
  | nil => exact StepGapChain.nil _
  | cons unused radius stage final last tail hgap hdiv hbound hminimum hcard hmatch hsub hrest ih =>
    exact StepGapChain.cons radius stage tail hdiv (by omega) ih

/-- Growing selections extend a supplied complete physical-label grid up to
exactly the final radius, conditional on its freshness. -/
theorem BTGrowingTrace.extend_step_grid {g Q : ℕ} {unused final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q unused radius final last stages)
    (base : Finset BTSelectedStage) (hg : 0 < g) (hQ : 0 < Q)
    (hbase : CompleteStepGrid base BTSelectedStage.gap g radius)
    (hdiv : g ∣ radius) (hfresh : ∀ stage ∈ stages, stage ∉ base) :
    CompleteStepGrid (base ∪ stages.toFinset) BTSelectedStage.gap g last := by
  have h := extend_step_gap_chain BTSelectedStage.gap g base radius stages hg hbase hdiv
    (trace.nodup hQ) hfresh trace.step_gap_chain
  rw [trace.final_accounting.2.2]
  exact h

end
end Sude
