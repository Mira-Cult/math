import Sude.BTNarrowIteration
import Sude.PrefixLabelSelectionAdapter

/-! PD2 applied to the actual labelled low endpoints of a narrowed growth trace. -/
namespace Sude
noncomputable section

/-- The midpoint belonging to a low endpoint of a selected stage. -/
def growthStageMidpoint (stage : BTSelectedStage) (p : ℕ) : ℝ :=
  ((p : ℝ) + (p + stage.gap : ℕ)) / 2

/-- For a narrowed growth trace, select exactly `k` actual low endpoints per
stage with one aggregate half-width error. Stages are indexed by occurrences
in the trace, preserving their identity even if values coincide. This does
not construct physical slot assignments. -/
theorem fw_growth_narrow_pd2 {n : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6 * (n + 8)) initial radius final last stages)
    (X : ℝ) (hX : 0 ≤ X) (hnarrow : NarrowedStages (X / 6) stages)
    (k : ℕ) (hk : k ≤ 6 * (n + 8)) :
    ∃ T : Fin stages.length → Finset ℕ,
      (∀ j, T j ⊆ (stages.get j).lows ∧ (T j).card = k) ∧
      |(∑ j, ∑ p ∈ T j, growthStageMidpoint (stages.get j) p) -
        (k : ℝ) * ∑ j, ((∑ p ∈ (stages.get j).lows,
          growthStageMidpoint (stages.get j) p) / (6 * (n + 8) : ℕ))| ≤ (X / 6) / 2 := by
  classical
  let s : Fin stages.length → Finset ℕ := fun j => (stages.get j).lows
  let x : Fin stages.length → ℕ → ℝ := fun j p => growthStageMidpoint (stages.get j) p
  have hc : ∀ j, (s j).card = 6 * (n + 8) := by
    intro j
    exact (trace.stage_properties _ (List.get_mem _ _)).2.2.2.1
  have hw : ∀ j, ∀ a ∈ s j, ∀ b ∈ s j, x j b - x j a ≤ X / 6 := by
    intro j a ha b hb
    have h := hnarrow (stages.get j) (List.get_mem _ _) b hb a ha
    exact le_of_lt (abs_lt.mp h).2
  obtain ⟨T, hT, hb⟩ := prefix_global_finset_select s k x (X / 6)
    (div_nonneg hX (by norm_num)) (fun j => by rw [hc j]; exact hk) hw
  refine ⟨T, hT, ?_⟩
  simpa only [s, x, hc] using hb

end
end Sude
