import Sude.FiniteIndependentBinaryMoment
import Sude.FiniteUniformStageMeasure
import Sude.FairBlockSwap

/-! A finite mixed moment for a uniform stage-permutation assignment followed
by independent fair block swaps. Endpoint data may depend on the assignment;
the interval and weights used for each coordinate are uniform over assignments.
This module does not assert any geometric placement or line concentration. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory

local instance stageFairSwapPermMeasurable (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- The average over whole stage assignments and all fair swap vectors is
bounded by the stage MGF times the product of the single-swap bounds. Each
swap coordinate shares one Boolean across its two weighted contributions. -/
theorem stage_fair_swap_exp_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r n : ℕ) (outer : (Fin r → Equiv.Perm (Fin n)) → ℝ)
    (x y : (Fin r → Equiv.Perm (Fin n)) → ι → ℝ)
    (w₁ w₂ lo hi : ι → ℝ) (t : ℝ)
    (hx : ∀ a i, x a i ∈ Set.Icc (lo i) (hi i))
    (hy : ∀ a i, y a i ∈ Set.Icc (lo i) (hi i)) :
    (∑ a, ∑ ω : ι → Bool, Real.exp (t * (outer a + ∑ i,
      (fairBlockSwapValue (x a i) (y a i) (w₁ i) (w₂ i) (ω i) -
        (w₁ i + w₂ i) * (x a i + y a i) / 2)))) /
      ((Fintype.card (Fin r → Equiv.Perm (Fin n)) : ℝ) * (2 : ℝ) ^ Fintype.card ι) ≤
      mgf outer (stagePermutationMeasure r n) t *
        ∏ i, Real.exp (t ^ 2 * ((w₁ i - w₂ i) ^ 2 * (hi i - lo i) ^ 2 / 4) / 2) := by
  classical
  rw [stage_permutation_mgf_eq_average]
  refine finite_outer_binary_exp_moment outer
    (fun a i b => fairBlockSwapValue (x a i) (y a i) (w₁ i) (w₂ i) b -
      (w₁ i + w₂ i) * (x a i + y a i) / 2)
    (fun i => Real.exp (t ^ 2 * ((w₁ i - w₂ i) ^ 2 * (hi i - lo i) ^ 2 / 4) / 2) ) t ?_
  intro a i
  exact fair_block_swap_centered_mgf_bound (x a i) (y a i) (w₁ i) (w₂ i)
    (lo i) (hi i) t (hx a i) (hy a i)


/-- Combining the swap bound with the existing sub-Gaussian estimate for
weighted, independently permuted stages gives a finite mixed moment bound.
The asserted average uses a uniform swap vector for every stage assignment. -/
theorem stage_weighted_fair_swap_exp_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r n : ℕ} (slots : Fin r → Finset (Fin n))
    (weights values : Fin r → Fin n → ℝ) (stageLo stageHi : Fin r → ℝ)
    (x y : (Fin r → Equiv.Perm (Fin n)) → ι → ℝ)
    (w₁ w₂ lo hi : ι → ℝ) (t : ℝ)
    (hnonneg : ∀ i j, j ∈ slots i → 0 ≤ weights i j)
    (hvalues : ∀ i a, values i a ∈ Set.Icc (stageLo i) (stageHi i))
    (hx : ∀ a i, x a i ∈ Set.Icc (lo i) (hi i))
    (hy : ∀ a i, y a i ∈ Set.Icc (lo i) (hi i)) :
    (∑ a, ∑ ω : ι → Bool, Real.exp (t *
      ((∑ j, stageWeightedCentered slots weights values j (a j)) + ∑ i,
      (fairBlockSwapValue (x a i) (y a i) (w₁ i) (w₂ i) (ω i) -
        (w₁ i + w₂ i) * (x a i + y a i) / 2)))) /
      ((Fintype.card (Fin r → Equiv.Perm (Fin n)) : ℝ) * (2 : ℝ) ^ Fintype.card ι) ≤
      Real.exp (((stageWeightedProxy slots weights stageLo stageHi : NNReal) : ℝ) * t ^ 2 / 2) *
        ∏ i, Real.exp (t ^ 2 * ((w₁ i - w₂ i) ^ 2 * (hi i - lo i) ^ 2 / 4) / 2) := by
  classical
  calc
    _ ≤ mgf (fun a => ∑ j, stageWeightedCentered slots weights values j (a j))
          (stagePermutationMeasure r n) t *
        ∏ i, Real.exp (t ^ 2 * ((w₁ i - w₂ i) ^ 2 * (hi i - lo i) ^ 2 / 4) / 2) :=
      stage_fair_swap_exp_moment r n _ x y w₁ w₂ lo hi t hx hy
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right
      · exact (stageWeighted_hasSubgaussian slots weights values stageLo stageHi hnonneg hvalues).mgf_le t
      · exact Finset.prod_nonneg (fun i _ => le_of_lt (Real.exp_pos _))

end
end Sude
