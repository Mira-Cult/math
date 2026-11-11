import Sude.FWGrowthNarrowPD2
import Sude.PrefixThreeSelections

/-! Joint PD3--PD6 selections from the actual narrowed growth trace.
This chooses source labels; physical allocation is a separate obligation. -/
namespace Sude
noncomputable section

/-- On the same supplied growing trace, select 12, 12 and 24 distinct
low-endpoint labels per stage. Their aggregate errors are measured against
the original stage means and satisfy the PD3--PD6 bounds at width `X/6`.
No physical slot assignment or line-sum bound is asserted. -/
theorem fw_growth_three_global_selections {n : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6 * (n + 8)) initial radius final last stages)
    (hn : 3 ≤ n) (X : ℝ) (hX : 0 ≤ X)
    (hnarrow : NarrowedStages (X / 6) stages) :
    ∃ T U V : Fin stages.length → Finset ℕ,
      (∀ j, T j ⊆ (stages.get j).lows ∧ U j ⊆ (stages.get j).lows \ T j ∧
        V j ⊆ (stages.get j).lows \ (T j ∪ U j) ∧
        (T j).card = 12 ∧ (U j).card = 12 ∧ (V j).card = 24) ∧
      let μ := fun j => (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) /
        (6 * (n+8) : ℕ)
      let E1 := (∑ j, ∑ p ∈ T j, growthStageMidpoint (stages.get j) p) - (12 : ℝ) * ∑ j, μ j
      let D2 := (∑ j, ∑ p ∈ U j, growthStageMidpoint (stages.get j) p) - (12 : ℝ) * ∑ j, μ j
      let E2 := (∑ j, ∑ p ∈ T j ∪ U j, growthStageMidpoint (stages.get j) p) - (24 : ℝ) * ∑ j, μ j
      let E3 := (∑ j, ∑ p ∈ (T j ∪ U j) ∪ V j, growthStageMidpoint (stages.get j) p) - (48 : ℝ) * ∑ j, μ j
      |E1| ≤ (X/6)/2 ∧ |D2| ≤ ((n+8 : ℝ)/(2*(n+6)))*(X/6) ∧
        |E2| ≤ ((n+5 : ℝ)/(n+6))*(X/6) ∧ |E3| ≤ (3/2:ℝ)*(X/6) ∧
        (0 < X/6 → |E3| < (3/2:ℝ)*(X/6)) := by
  classical
  let A : Fin stages.length → Finset ℕ := fun j => (stages.get j).lows
  let v : Fin stages.length → ℕ → ℝ := fun j p => growthStageMidpoint (stages.get j) p
  have hc : ∀ j, (A j).card = 6 * (n+8) := by
    intro j
    exact (trace.stage_properties _ (List.get_mem _ _)).2.2.2.1
  have hw : ∀ j, ∀ a ∈ A j, ∀ b ∈ A j, v j b - v j a ≤ X/6 := by
    intro j a ha b hb
    exact le_of_lt ((abs_lt.mp (hnarrow (stages.get j) (List.get_mem _ _) b hb a ha)).2)
  have hs := prefix_three_global_selections A v n 6 (X/6) hn (by norm_num)
    (div_nonneg hX (by norm_num)) hc hw
  simpa only [A, v, Nat.reduceMul, Nat.cast_ofNat] using hs

end
end Sude
