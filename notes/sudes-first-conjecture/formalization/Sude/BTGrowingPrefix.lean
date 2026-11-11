import Sude.BTGrowthBounds

/-! Connect source phase inequalities to the evolving physical trace. -/
namespace Sude
noncomputable section

/-- The radius available before any listed stage is the initial radius plus
all preceding selected gaps, so that stage's gap obeys the correct bound. -/
theorem BTGrowingTrace.prefix_gap_bound {g Q : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial radius final last stages) :
    ∀ before stage after, stages = before ++ stage :: after →
      stage.gap ≤ radius + (before.map BTSelectedStage.gap).sum := by
  induction trace with
  | nil =>
    intro before stage after h
    cases before <;> simp at h
  | cons unused radius s final last tail hgap hdiv hbound hminimum hcard hmatch hsub hrest ih =>
    intro before stage after he
    cases before with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at he
      rcases he with ⟨rfl, _⟩
      simpa using hbound
    | cons x before =>
      simp only [List.cons_append, List.cons.injEq] at he
      rcases he with ⟨rfl, he⟩
      have hb := ih before stage after he
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Split a trace before an arbitrary stage. The middle stock is the actual
remaining stock after precisely the preceding physical pair deletions. -/
theorem BTGrowingTrace.split_at_stage {g Q : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial radius final last stages) :
    ∀ before stage after, stages = before ++ stage :: after →
      ∃ middle, BTGrowingTrace g Q initial radius middle
        (radius + (before.map BTSelectedStage.gap).sum) before ∧
        BTGrowingTrace g Q middle (radius + (before.map BTSelectedStage.gap).sum)
          final last (stage :: after) := by
  induction trace with
  | nil =>
    intro before stage after h
    cases before <;> simp at h
  | cons unused radius s final last tail hgap hdiv hbound hminimum hcard hmatch hsub hrest ih =>
    intro before stage after he
    cases before with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at he
      rcases he with ⟨rfl, rfl⟩
      refine ⟨unused, ?_⟩
      simpa using And.intro (BTGrowingTrace.nil (g := g) (Q := Q) unused radius)
        (BTGrowingTrace.cons unused radius s final last tail hgap hdiv hbound hminimum hcard hmatch hsub hrest)
    | cons x before =>
      simp only [List.cons_append, List.cons.injEq] at he
      rcases he with ⟨rfl, he⟩
      obtain ⟨middle, hp, hs⟩ := ih before stage after he
      refine ⟨middle, ?_, ?_⟩
      · have hc := BTGrowingTrace.cons unused radius s middle
          (radius + s.gap + (before.map BTSelectedStage.gap).sum) before
          hgap hdiv hbound hminimum hcard hmatch hsub hp
        simpa [add_assoc, add_comm, add_left_comm] using hc
      · simpa [add_assoc, add_comm, add_left_comm] using hs

/-- The exact stage stock is obtained by charging `2Q` entries per earlier
stage, and it still contains every endpoint used by the current stage. -/
theorem BTGrowingTrace.prefix_stock_accounting {g Q : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial radius final last stages)
    (before : List BTSelectedStage) (stage : BTSelectedStage) (after : List BTSelectedStage)
    (he : stages = before ++ stage :: after) :
    ∃ middle, middle ⊆ initial ∧ middle.card + 2 * Q * before.length = initial.card ∧
      stage.footprint ⊆ middle := by
  obtain ⟨middle, hp, hs⟩ := trace.split_at_stage before stage after he
  exact ⟨middle, hp.final_accounting.1, hp.final_accounting.2.1,
    hs.footprints_subset stage (by simp)⟩

/-- The source BT8 growth inequality applies to the actual stage in a trace
when that stage's recorded lower gap pays the displayed width. -/
theorem BTGrowingTrace.prefix_shifted_growth {g Q : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial radius final last stages)
    (before : List BTSelectedStage) (stage : BTSelectedStage) (after : List BTSelectedStage)
    (he : stages = before ++ stage :: after)
    (ζ η M Mf r X : ℝ) (hζ : 0 ≤ ζ) (hη : 0 < η) (hg : 0 ≤ (g : ℝ))
    (hMf : 0 < Mf) (hM : Mf ≤ M) (hr : 0 < r) (hX : 0 < X)
    (hwidth : ζ * g * (η * M *
      (radius + (before.map BTSelectedStage.gap).sum : ℕ) / (r * X) - 1 / 2) ≤ stage.minimum) :
    (1 + ζ * η * g * M / (r * X)) *
      ((radius + (before.map BTSelectedStage.gap).sum : ℕ) - r * X / (2 * η * Mf)) ≤
    ((radius + (before.map BTSelectedStage.gap).sum : ℕ) : ℝ) + stage.gap - r * X / (2 * η * Mf) := by
  have hmem : stage ∈ stages := by rw [he]; simp
  have hmin := (trace.stage_properties stage hmem).2.2.1
  exact bt_shifted_radius_growth ζ η g M Mf _ r X stage.gap hζ hη hg hMf hM hr hX
    (hwidth.trans hmin)

end
end Sude
