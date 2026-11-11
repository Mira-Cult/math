import Mathlib

/-! Exact cancellation of the common free-cell baseline for equal-size lines.
The line errors and reservation are supplied; no physical estimate is inferred. -/
namespace Sude
noncomputable section

/-- Equal line cardinalities cancel the common full-reservation free mean, even
when the two reserved intersection cardinalities differ. -/
theorem equal_card_centered_baseline_difference {α : Type*} [DecidableEq α]
    (A B R : Finset α) (v : α → ℝ) (μ : ℝ) (hcard : A.card = B.card) :
    ((∑ z ∈ A ∩ R, v z) + ((A \ R).card : ℝ) * μ) -
        ((∑ z ∈ B ∩ R, v z) + ((B \ R).card : ℝ) * μ) =
      (∑ z ∈ A ∩ R, (v z - μ)) - (∑ z ∈ B ∩ R, (v z - μ)) := by
  classical
  have hA : ((A \ R).card : ℝ) + ((A ∩ R).card : ℝ) = (A.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_inter A R
  have hB : ((B \ R).card : ℝ) + ((B ∩ R).card : ℝ) = (B.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_inter B R
  have hc : (A.card : ℝ) = (B.card : ℝ) := by exact_mod_cast hcard
  have hfree : ((A \ R).card : ℝ) - ((B \ R).card : ℝ) =
      ((B ∩ R).card : ℝ) - ((A ∩ R).card : ℝ) := by linarith
  have hm := congrArg (fun x : ℝ => x * μ) hfree
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  nlinarith [hm]

/-- Supplied line errors add to the absolute centered reservation difference. -/
theorem equal_card_centered_baseline_error {α : Type*} [DecidableEq α]
    (A B R : Finset α) (v : α → ℝ) (μ M N E₁ E₂ : ℝ) (hcard : A.card = B.card)
    (hM : |M - ((∑ z ∈ A ∩ R, v z) + ((A \ R).card : ℝ)*μ)| ≤ E₁)
    (hN : |N - ((∑ z ∈ B ∩ R, v z) + ((B \ R).card : ℝ)*μ)| ≤ E₂) :
    |M - N| ≤ |(∑ z ∈ A ∩ R, (v z - μ)) - (∑ z ∈ B ∩ R, (v z - μ))| + E₁ + E₂ := by
  let a := (∑ z ∈ A ∩ R, v z) + ((A \ R).card : ℝ)*μ
  let b := (∑ z ∈ B ∩ R, v z) + ((B \ R).card : ℝ)*μ
  have hab : a - b = (∑ z ∈ A ∩ R, (v z - μ)) - (∑ z ∈ B ∩ R, (v z - μ)) :=
    equal_card_centered_baseline_difference A B R v μ hcard
  have ht := abs_sub_le M a N
  have ht2 := abs_sub_le a b N
  rw [abs_sub_comm b N, hab] at ht2
  change |M-a| ≤ E₁ at hM
  change |N-b| ≤ E₂ at hN
  linarith

end
end Sude
