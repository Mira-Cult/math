import Sude.StageHalfGapCancellation
import Sude.JointStageSwapEventSelection

/-! One joint stage/swap selection with an explicit midpoint failure budget
and a proved signed-gap concentration bound. Physical slot geometry and an
actual midpoint-failure invoice remain separate obligations. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory

local instance jointMidGapPermMeasurable (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- Given a midpoint bad event of probability at most one half on the same
joint permutation/swap space, two equal-sized 12-slot gap samples are jointly
controlled on one permutation and one swap vector. Every source gap is
assumed to lie in the stated full-domain interval. -/
theorem joint_stage_midpoint_gap_selection {W B : ℕ}
    (hW : 0 < W) (hB : 24 ≤ B) (Δ : ℝ) (hΔ : 0 < Δ)
    (slots : Bool → Fin W → Finset (Fin B))
    (hcard : ∀ side j, (slots side j).card = 12)
    (hdisjoint : ∀ j, Disjoint (slots true j) (slots false j))
    (values : Fin W → Fin B → ℝ) (lo hi : Fin W → ℝ)
    (hwidth : ∀ j, hi j - lo j = Δ)
    (hvalues : ∀ j b, values j b ∈ Set.Icc (lo j) (hi j))
    (midBad : Set ((Fin W → Equiv.Perm (Fin B)) × ((Fin W × Fin B) → Bool)))
    (hmid : ((stagePermutationMeasure W B).prod
      (uniformOn (Set.univ : Set ((Fin W × Fin B) → Bool)))).real midBad ≤ (1/2 : ℝ)) :
    ∃ π swaps, (π,swaps) ∉ midBad ∧
      |(1/2 : ℝ) * ((∑ j, ∑ b ∈ slots true j, values j (π j b)) -
        ∑ j, ∑ b ∈ slots false j, values j (π j b))| <
          2 * Real.sqrt ((3/2 : ℝ) * W * Δ^2 * Real.log 16) := by
  classical
  let v : ℝ := (3/4 : ℝ) * W * Δ^2
  let e : ℝ := Real.sqrt (2 * v * Real.log 16)
  have hv : 0 < v := by dsimp [v]; positivity
  have hlog : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have he : 0 < e := by dsimp [e]; positivity
  have heq : e^2 = 2 * v * Real.log 16 := by
    dsimp [e]
    exact Real.sq_sqrt (by positivity)
  have htail : 2 * Real.exp (-e^2 / (2*v)) = (1/8 : ℝ) := by
    rw [heq]
    have hcalc : -(2 * v * Real.log 16) / (2 * v) = -Real.log 16 := by
      field_simp [ne_of_gt hv] <;> ring
    rw [hcalc, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
    norm_num
  let bad : Bool → Set (Fin W → Equiv.Perm (Fin B)) := fun side =>
    {π | e ≤ |stageHalfGapScore (slots side) values π|}
  have hbad (side : Bool) : (stagePermutationMeasure W B).real (bad side) ≤ (1/8 : ℝ) := by
    have hh := stage_half_gap_two_sided (slots side) values lo hi Δ e (le_of_lt hΔ)
      hwidth (hcard side) hvalues (le_of_lt he)
    change (stagePermutationMeasure W B).real (bad side) ≤ 2 * Real.exp (-e^2 / (2*v)) at hh
    simpa only [htail] using hh
  obtain ⟨π,swaps,hgood,hleft,hright⟩ := stage_swap_three_events_select midBad bad hmid hbad
  have hl : |stageHalfGapScore (slots true) values π| < e := lt_of_not_ge hleft
  have hr : |stageHalfGapScore (slots false) values π| < e := lt_of_not_ge hright
  have hd := stage_half_gap_score_difference (by omega : 0 < B) (slots true) (slots false) values π
    (fun j => by rw [hcard true j, hcard false j])
  refine ⟨π,swaps,hgood, ?_⟩
  rw [← hd]
  have habs := abs_sub (stageHalfGapScore (slots true) values π) (stageHalfGapScore (slots false) values π)
  have hevalue : e = Real.sqrt ((3/2 : ℝ) * W * Δ^2 * Real.log 16) := by
    dsimp [e,v]
    congr 1
    ring
  rw [← hevalue]
  linarith

end
end Sude
