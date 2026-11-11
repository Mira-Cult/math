import Sude.CentralStock
import Sude.CentralDiagonalBounds

/-! CC3's two diagonal deviations for the actual successive selected sets. -/
namespace Sude
noncomputable section

/-- Both labelled diagonal batches include the same center exactly once.
Under CC1's stock size and the three individual selection-error bounds, their
deviations from the original mean are at most `2η` and `201η/100`. -/
theorem central_actual_diagonal_errors {α : Type*} [DecidableEq α]
    (unused A B C : Finset α) (value : α → ℝ) (n q₁ q₂ : ℕ) (η : ℝ)
    (hn : 20 ≤ n) (hN : 3 * n * n ≤ 4 * unused.card)
    (hq₁ : q₁ ≤ n - 1) (hq₂ : q₂ ≤ n - 1) (hη : 0 ≤ η)
    (hA : A ⊆ unused) (hB : B ⊆ unused \ A) (hC : C ⊆ (unused \ A) \ B)
    (hcA : A.card = 1) (hcB : B.card = q₁) (hcC : C.card = q₂)
    (he₀ : |(∑ a ∈ A, value a) - centralEntriesMean unused value| ≤ η)
    (he₁ : |(∑ a ∈ B, value a) - (q₁ : ℝ) * centralEntriesMean (unused \ A) value| ≤ η)
    (he₂ : |(∑ a ∈ C, value a) - (q₂ : ℝ) * centralEntriesMean ((unused \ A) \ B) value| ≤ η) :
    |(∑ a ∈ A ∪ B, value a) - ((1 + q₁ : ℕ) : ℝ) * centralEntriesMean unused value| ≤ 2 * η ∧
      |(∑ a ∈ A ∪ C, value a) - ((1 + q₂ : ℕ) : ℝ) * centralEntriesMean unused value| ≤
        (201 / 100) * η := by
  classical
  let S₁ := unused \ A
  let S₂ := S₁ \ B
  let μ₀ := centralEntriesMean unused value
  let μ₁ := centralEntriesMean S₁ value
  let μ₂ := centralEntriesMean S₂ value
  let e₀ := (∑ a ∈ A, value a) - μ₀
  let e₁ := (∑ a ∈ B, value a) - (q₁ : ℝ) * μ₁
  let e₂ := (∑ a ∈ C, value a) - (q₂ : ℝ) * μ₂
  have hc₁ : S₁.card + 1 = unused.card := by
    simpa [S₁, hcA] using Finset.card_sdiff_add_card_eq_card hA
  have hc₂ : S₂.card + q₁ = S₁.card := by
    simpa [S₂, hcB] using Finset.card_sdiff_add_card_eq_card hB
  have hd := central_diagonal_source_denominators n unused.card S₁.card S₂.card q₁ hn hN hq₁ hc₁ hc₂
  have hd₁ : (7 : ℝ) * (n : ℝ) * n ≤ 10 * (S₁.card : ℝ) := by exact_mod_cast hd.1
  have hd₂ : (7 : ℝ) * (n : ℝ) * n ≤ 10 * (S₂.card : ℝ) := by exact_mod_cast hd.2
  have hN₁ : (7 / 10 : ℝ) * (n : ℝ) ^ 2 ≤ (S₁.card : ℝ) := by nlinarith
  have hN₂ : (7 / 10 : ℝ) * (n : ℝ) ^ 2 ≤ (S₂.card : ℝ) := by nlinarith
  have hq₁' : (q₁ : ℝ) ≤ n := by exact_mod_cast (show q₁ ≤ n by omega)
  have hq₂' : (q₂ : ℝ) ≤ n := by exact_mod_cast (show q₂ ≤ n by omega)
  have hratio := central_diagonal_source_ratio (n : ℝ) (S₁.card : ℝ) (S₂.card : ℝ)
    (q₁ : ℝ) (q₂ : ℝ) (by exact_mod_cast hn) ⟨by positivity, hq₁'⟩ ⟨by positivity, hq₂'⟩ hN₁ hN₂
  have hpos₁ : 0 < S₁.card := by exact_mod_cast hratio.1
  have hpos₂ : 0 < S₂.card := by exact_mod_cast hratio.2.1
  have hcount : (S₁.card : ℝ) = (S₂.card : ℝ) + (q₁ : ℝ) := by exact_mod_cast hc₂.symm
  have hm₁ : μ₁ = μ₀ - e₀ / (S₁.card : ℝ) := by
    simpa [S₁, μ₀, μ₁, e₀, hcA] using central_entries_actual_mean_update unused A value hA hpos₁
  have hm₂ : μ₂ = μ₁ - e₁ / (S₂.card : ℝ) := by
    simpa [S₂, μ₁, μ₂, e₁, hcB] using central_entries_actual_mean_update S₁ B value hB hpos₂
  have hscalar := central_diagonal_scalar_bounds (S₁.card : ℝ) (S₂.card : ℝ) (q₁ : ℝ) (q₂ : ℝ)
    e₀ e₁ e₂ η hratio.1 hratio.2.1 (by positivity) (by positivity) hcount hratio.2.2.1
    hratio.2.2.2 hη he₀ he₁ he₂
  have hident := central_diagonal_error_identities (S₁.card : ℝ) (S₂.card : ℝ) (q₁ : ℝ) (q₂ : ℝ)
    μ₀ μ₁ μ₂ e₀ e₁ e₂ hm₁ hm₂
  have hab : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_sdiff.mp (hB hb)).2 ha
  have hac : Disjoint A C := by
    apply Finset.disjoint_left.mpr
    intro a ha hc
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hC hc)).1).2 ha
  have hform₁ : (∑ a ∈ A, value a) + (∑ a ∈ B, value a) - ((1 + q₁ : ℕ) : ℝ) * μ₀ =
      e₀ + e₁ + (q₁ : ℝ) * (μ₁ - μ₀) := by
    dsimp [e₀, e₁]
    push_cast
    ring
  have hform₂ : (∑ a ∈ A, value a) + (∑ a ∈ C, value a) - ((1 + q₂ : ℕ) : ℝ) * μ₀ =
      e₀ + e₂ + (q₂ : ℝ) * (μ₂ - μ₀) := by
    dsimp [e₀, e₂]
    push_cast
    ring
  constructor
  · rw [Finset.sum_union hab, hform₁, hident.1]
    exact hscalar.1
  · rw [Finset.sum_union hac, hform₂, hident.2]
    exact hscalar.2

end
end Sude
