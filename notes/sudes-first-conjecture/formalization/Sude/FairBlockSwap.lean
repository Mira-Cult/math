import Sude.PermutationHoeffding
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! The fair internal swap of one selected double block. Both weighted
contributions use the same Boolean outcome, retaining their correlation.
No multi-block or stage concentration claim is made. -/
namespace Sude
noncomputable section

/-- The two weighted values under one shared swap decision. -/
def fairBlockSwapValue (x y w₁ w₂ : ℝ) (swap : Bool) : ℝ :=
  if swap then w₁ * y + w₂ * x else w₁ * x + w₂ * y

/-- The exact mean of the two equally likely swap outcomes. -/
theorem fair_block_swap_mean (x y w₁ w₂ : ℝ) :
    (fairBlockSwapValue x y w₁ w₂ false + fairBlockSwapValue x y w₁ w₂ true) / 2 =
      (w₁ + w₂) * (x + y) / 2 := by
  simp only [fairBlockSwapValue, Bool.false_eq_true, ↓reduceIte]
  ring

/-- Both outcomes have the same exact centered magnitude, including the
cancellation between the two weighted contributions. -/
theorem fair_block_swap_centered_abs (x y w₁ w₂ : ℝ) (swap : Bool) :
    |fairBlockSwapValue x y w₁ w₂ swap - (w₁ + w₂) * (x + y) / 2| =
      |(w₁ - w₂) * (x - y)| / 2 := by
  cases swap
  · have h : fairBlockSwapValue x y w₁ w₂ false - (w₁ + w₂) * (x + y) / 2 =
        ((w₁ - w₂) * (x - y)) / 2 := by
      simp only [fairBlockSwapValue, Bool.false_eq_true, ↓reduceIte]
      ring
    rw [h, abs_div]
    norm_num
  · have h : fairBlockSwapValue x y w₁ w₂ true - (w₁ + w₂) * (x + y) / 2 =
        -((w₁ - w₂) * (x - y)) / 2 := by
      simp only [fairBlockSwapValue, ↓reduceIte]
      ring
    rw [h, abs_div, abs_neg]
    norm_num

/-- For any two values in the same interval and arbitrary real weights,
the fair two-outcome conditional exponential moment is sub-Gaussian.
The conditional law is represented by the explicit equal-weight average;
its single shared swap preserves the correlation of the two contributions. -/
theorem fair_block_swap_centered_mgf_bound (x y w₁ w₂ lo hi t : ℝ)
    (hx : x ∈ Set.Icc lo hi) (hy : y ∈ Set.Icc lo hi) :
    let mean := (w₁ + w₂) * (x + y) / 2
    (Real.exp (t * (fairBlockSwapValue x y w₁ w₂ false - mean)) +
      Real.exp (t * (fairBlockSwapValue x y w₁ w₂ true - mean))) / 2 ≤
      Real.exp (t ^ 2 * ((w₁ - w₂) ^ 2 * (hi - lo) ^ 2 / 4) / 2) := by
  dsimp only
  have hfalse : fairBlockSwapValue x y w₁ w₂ false - (w₁ + w₂) * (x + y) / 2 =
      (w₁ - w₂) * (x - y) / 2 := by
    simp only [fairBlockSwapValue, Bool.false_eq_true, ↓reduceIte]
    ring
  have htrue : fairBlockSwapValue x y w₁ w₂ true - (w₁ + w₂) * (x + y) / 2 =
      -((w₁ - w₂) * (x - y) / 2) := by
    simp only [fairBlockSwapValue, ↓reduceIte]
    ring
  rw [hfalse, htrue]
  have hdiff : (x - y) ^ 2 ≤ (hi - lo) ^ 2 := by
    have ha : |x - y| ≤ hi - lo := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have hspan : 0 ≤ hi - lo := by linarith [hx.1, hx.2]
    nlinarith [sq_abs (x - y), abs_nonneg (x - y)]
  calc
    _ = Real.cosh (t * ((w₁ - w₂) * (x - y) / 2)) := by
      simp only [Real.cosh_eq, mul_neg]
    _ ≤ Real.exp ((t * ((w₁ - w₂) * (x - y) / 2)) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sq_nonneg t) (mul_nonneg (sq_nonneg (w₁ - w₂)) (sub_nonneg.mpr hdiff))]

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- The mean under any probability measure on which the shared measurable
Boolean swap remains fair. In particular, the measure may be a conditional
history measure, provided the displayed fairness hypothesis holds there. -/
theorem fair_block_swap_conditional_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (flip : Ω → Bool) (hf : Measurable flip)
    (hfair : μ[fun ω => if flip ω then (1:ℝ) else 0] = 1/2)
    (x y w₁ w₂ : ℝ) :
    μ[(fun ω => fairBlockSwapValue x y w₁ w₂ (flip ω))] = (w₁ + w₂) * (x + y) / 2 := by
  let z : Ω → ℝ := fun ω => if flip ω then 1 else 0
  have hm : Measurable z := by
    dsimp [z]
    exact measurable_const.ite (hf (measurableSet_singleton true)) measurable_const
  have hi : Integrable z μ := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards with ω
    dsimp [z]
    split_ifs <;> norm_num
  have heq : (fun ω => fairBlockSwapValue x y w₁ w₂ (flip ω)) = fun ω =>
      (w₁*x+w₂*y) + ((w₁*y+w₂*x)-(w₁*x+w₂*y))*z ω := by
    funext ω
    dsimp [fairBlockSwapValue,z]
    split_ifs <;> ring
  rw [heq, integral_add (integrable_const _) (hi.const_mul _), integral_const, integral_const_mul]
  simp only [measure_univ, measureReal_def, ENNReal.toReal_one, one_smul]
  change _ + _ * (∫ ω, (if flip ω then (1:ℝ) else 0) ∂μ) = _
  rw [hfair]
  ring


/-- Hoeffding's centered MGF bound for a fair single internal block swap. -/
theorem fair_block_swap_conditional_subgaussian {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (flip : Ω → Bool) (hf : Measurable flip)
    (hfair : μ[fun ω => if flip ω then (1:ℝ) else 0] = 1/2)
    (x y w₁ w₂ low upper : ℝ) (hx : x ∈ Set.Icc low upper) (hy : y ∈ Set.Icc low upper) :
    HasSubgaussianMGF
      (fun ω => fairBlockSwapValue x y w₁ w₂ (flip ω) - (w₁ + w₂) * (x + y) / 2)
      ((‖|w₁-w₂| * (upper-low)‖₊ / 2) ^ 2) μ := by
  let center := (w₁+w₂)*(x+y)/2
  let width := |w₁-w₂| * (upper-low)
  have hxy : |x-y| ≤ upper-low := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hd : |(w₁-w₂)*(x-y)| ≤ width := by
    dsimp [width]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hxy (abs_nonneg _)
  have hm : Measurable (fun ω => fairBlockSwapValue x y w₁ w₂ (flip ω)) := by
    change Measurable (fun ω => if flip ω then w₁ * y + w₂ * x else w₁ * x + w₂ * y)
    exact measurable_const.ite (hf (measurableSet_singleton true)) measurable_const
  have hb : ∀ᵐ ω ∂μ, fairBlockSwapValue x y w₁ w₂ (flip ω) ∈ Set.Icc (center-width/2) (center+width/2) := by
    filter_upwards with ω
    have hh := abs_le.mp hd
    dsimp [fairBlockSwapValue,center]
    split_ifs <;> constructor <;> nlinarith [hh.1, hh.2]
  have h := hasSubgaussianMGF_of_mem_Icc hm.aemeasurable hb
  rw [fair_block_swap_conditional_mean μ flip hf hfair x y w₁ w₂] at h
  have hw : center+width/2 - (center-width/2) = width := by ring
  rw [hw] at h
  exact h


end
end Sude
