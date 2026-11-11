import Sude.BTGrowingCompose

/-! The paid initial target persists through later nondecreasing radii. -/
namespace Sude
noncomputable section

/-- If an earlier phase paid BT7, every later state of a growing trace still
satisfies the BT phase-entry inequality, provided its stock remains above the
terminal floor. -/
theorem BTGrowingTrace.phase_entry_persists {g Q : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial radius final last stages)
    (ζ η M Mf r X ell : ℝ) (hζ : 0 < ζ) (hη : 0 < η) (hg : 0 < g)
    (hMf : 0 < Mf) (hM : Mf ≤ M) (hr : 0 < r) (hX : 0 < X)
    (hpaid : r * X * Real.exp ell / (ζ * η * Mf) ≤
      (radius : ℝ) - r * X / (2 * η * Mf)) :
    Real.exp ell ≤ (ζ * g * (η * M * (last : ℝ) / (r * X) - 1 / 2)) / g := by
  have hlast : radius ≤ last := by
    rw [trace.final_accounting.2.2]
    omega
  have hlastR : (radius : ℝ) ≤ last := by exact_mod_cast hlast
  have hpaid' : r * X * Real.exp ell / (ζ * η * Mf) ≤
      (last : ℝ) - r * X / (2 * η * Mf) := by linarith
  exact bt_phase_entry ζ η g M Mf last r X ell hζ hη (by exact_mod_cast hg) hMf hM hr hX hpaid'

/-- BT7 remains paid at an arbitrary selected stage, not only at the end of
a phase. The applicable stock lower bound is a separate explicit input. -/
theorem BTGrowingTrace.phase_entry_at_stage {g Q : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial radius final last stages)
    (before : List BTSelectedStage) (stage : BTSelectedStage) (after : List BTSelectedStage)
    (he : stages = before ++ stage :: after)
    (ζ η M Mf r X ell : ℝ) (hζ : 0 < ζ) (hη : 0 < η) (hg : 0 < g)
    (hMf : 0 < Mf) (hM : Mf ≤ M) (hr : 0 < r) (hX : 0 < X)
    (hpaid : r * X * Real.exp ell / (ζ * η * Mf) ≤
      (radius : ℝ) - r * X / (2 * η * Mf)) :
    Real.exp ell ≤ (ζ * g * (η * M *
      (radius + (before.map BTSelectedStage.gap).sum : ℕ) / (r * X) - 1 / 2)) / g := by
  obtain ⟨middle, hprefix, _⟩ := trace.split_at_stage before stage after he
  exact hprefix.phase_entry_persists ζ η M Mf r X ell hζ hη hg hMf hM hr hX hpaid

end
end Sude
