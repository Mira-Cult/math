import Sude.CentralStock
import Sude.CentralAccounting

/-! Apply the CC10 signed-error identity to actual successive stock sets. -/
namespace Sude
noncomputable section

/-- Three disjoint, successively selected batches whose individual sums are
within `η` of their respective current means have aggregate signed error at
most `3η` relative to the original mean. The third deletion leaves entries. -/
theorem central_actual_three_batch_error {α : Type*} [DecidableEq α]
    (unused A B C : Finset α) (value : α → ℝ) (η : ℝ)
    (hA : A ⊆ unused) (hB : B ⊆ unused \ A) (hC : C ⊆ (unused \ A) \ B)
    (hpos : 0 < (((unused \ A) \ B) \ C).card) (hη : 0 ≤ η)
    (he₀ : |(∑ a ∈ A, value a) - (A.card : ℝ) * centralEntriesMean unused value| ≤ η)
    (he₁ : |(∑ a ∈ B, value a) - (B.card : ℝ) * centralEntriesMean (unused \ A) value| ≤ η)
    (he₂ : |(∑ a ∈ C, value a) - (C.card : ℝ) * centralEntriesMean ((unused \ A) \ B) value| ≤ η) :
    |(∑ a ∈ A, value a) + (∑ a ∈ B, value a) + (∑ a ∈ C, value a) -
      ((A.card + B.card + C.card : ℕ) : ℝ) * centralEntriesMean unused value| ≤ 3 * η := by
  let S₁ := unused \ A
  let S₂ := S₁ \ B
  let S₃ := S₂ \ C
  let μ₀ := centralEntriesMean unused value
  let μ₁ := centralEntriesMean S₁ value
  let μ₂ := centralEntriesMean S₂ value
  let e₀ := (∑ a ∈ A, value a) - (A.card : ℝ) * μ₀
  let e₁ := (∑ a ∈ B, value a) - (B.card : ℝ) * μ₁
  let e₂ := (∑ a ∈ C, value a) - (C.card : ℝ) * μ₂
  have hS₃ : S₃ ⊆ S₂ := Finset.sdiff_subset
  have hS₂ : S₂ ⊆ S₁ := Finset.sdiff_subset
  have hpos₂ : 0 < S₂.card := lt_of_lt_of_le hpos (Finset.card_le_card hS₃)
  have hpos₁ : 0 < S₁.card := lt_of_lt_of_le hpos₂ (Finset.card_le_card hS₂)
  have hN₁ : (0 : ℝ) < (S₁.card : ℝ) := by exact_mod_cast hpos₁
  have hN₂ : (0 : ℝ) < (S₂.card : ℝ) := by exact_mod_cast hpos₂
  have hN₃ : (0 : ℝ) ≤ (S₃.card : ℝ) := by positivity
  have hc₁ : (S₁.card : ℝ) = (S₂.card : ℝ) + (B.card : ℝ) := by
    exact_mod_cast (Finset.card_sdiff_add_card_eq_card hB).symm
  have hc₂ : (S₂.card : ℝ) = (S₃.card : ℝ) + (C.card : ℝ) := by
    exact_mod_cast (Finset.card_sdiff_add_card_eq_card hC).symm
  have hm₁ : μ₁ = μ₀ - e₀ / (S₁.card : ℝ) :=
    central_entries_actual_mean_update unused A value hA hpos₁
  have hm₂ : μ₂ = μ₁ - e₁ / (S₂.card : ℝ) :=
    central_entries_actual_mean_update S₁ B value hB hpos₂
  have hb := central_three_error_bound (S₁.card : ℝ) (S₂.card : ℝ) (S₃.card : ℝ)
    (B.card : ℝ) (C.card : ℝ) μ₀ μ₁ μ₂ e₀ e₁ e₂ η hN₁ hN₂ hN₃
    (by positivity) (by positivity) hc₁ hc₂ hm₁ hm₂ hη he₀ he₁ he₂
  have heq : (∑ a ∈ A, value a) + (∑ a ∈ B, value a) + (∑ a ∈ C, value a) -
      ((A.card + B.card + C.card : ℕ) : ℝ) * μ₀ =
      e₀ + (e₁ + (B.card : ℝ) * (μ₁ - μ₀)) + (e₂ + (C.card : ℝ) * (μ₂ - μ₀)) := by
    dsimp [e₀, e₁, e₂]
    push_cast
    ring
  rw [heq]
  exact hb

end
end Sude
