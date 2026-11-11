import Sude.CentralBatch

/-! Persistence for the three successive central batches in CC2. -/
namespace Sude
noncomputable section

/-- CC1--CC2's original quadratic stock size supplies the reserve required
for the center and the two batches of at most `n - 1` entries. -/
theorem central_source_reserve (n N q₁ q₂ : ℕ) (hn : 20 ≤ n)
    (hN : 3 * n * n ≤ 4 * N) (hq₁ : q₁ ≤ n - 1) (hq₂ : q₂ ≤ n - 1) :
    13 ≤ n * n / 2 ∧ 1 + q₁ + q₂ + n * n / 2 ≤ N := by
  have hmod : n * n % 2 < 2 := Nat.mod_lt _ (by decide)
  have hdiv : n * n = (n * n / 2) * 2 + n * n % 2 := by omega
  have hq₁' : q₁ + 1 ≤ n := by omega
  have hq₂' : q₂ + 1 ≤ n := by omega
  have hsq : 8 * n ≤ n * n := by nlinarith
  have hq : 1 + q₁ + q₂ ≤ 2 * n := by omega
  have hquad : 4 * (1 + q₁ + q₂) ≤ n * n := by nlinarith
  have hN' : 3 * (n * n) ≤ 4 * N := by simpa only [mul_assoc] using hN
  have hhalf : 2 * (n * n / 2) ≤ n * n := by omega
  constructor
  · nlinarith
  · omega

/-- The center and two diagonal batches can be selected successively from
the actual remaining entries. Both outer stocks pay for every previous
deletion. A reserve of 13 entries suffices for the two mean shifts used
before the later selections; source-specific quadratic bounds can supply
the stronger reserve separately. Zero-size batches are allowed. -/
theorem central_three_batches {α : Type*} [DecidableEq α]
    (unused : Finset α) (value : α → ℝ) (hinj : Set.InjOn value (↑unused : Set α))
    (q₀ q₁ q₂ K : ℕ) (c η : ℝ) (hη : 0 < η) (hK : 13 ≤ K)
    (hreserve : q₀ + q₁ + q₂ + K ≤ unused.card)
    (hmean : |centralEntriesMean unused value - c| ≤ η / 4)
    (hlow : q₀ + q₁ + q₂ ≤
      (unused.filter (fun a => c - η < value a ∧ value a ≤ c - η / 2)).card)
    (hhigh : q₀ + q₁ + q₂ ≤
      (unused.filter (fun a => c + η / 2 < value a ∧ value a ≤ c + η)).card) :
    ∃ A B C : Finset α,
      A ⊆ unused ∧ B ⊆ unused \ A ∧ C ⊆ (unused \ A) \ B ∧
      A.card = q₀ ∧ B.card = q₁ ∧ C.card = q₂ ∧
      (∀ a ∈ A ∪ B ∪ C, |value a - c| ≤ η) ∧
      |(∑ a ∈ A, value a) - (q₀ : ℝ) * centralEntriesMean unused value| ≤ η ∧
      |(∑ a ∈ B, value a) - (q₁ : ℝ) * centralEntriesMean (unused \ A) value| ≤ η ∧
      |(∑ a ∈ C, value a) - (q₂ : ℝ) * centralEntriesMean ((unused \ A) \ B) value| ≤ η ∧
      K ≤ (((unused \ A) \ B) \ C).card := by
  let low : α → Prop := fun a => c - η < value a ∧ value a ≤ c - η / 2
  let high : α → Prop := fun a => c + η / 2 < value a ∧ value a ≤ c + η
  classical
  change q₀ + q₁ + q₂ ≤ (unused.filter low).card at hlow
  change q₀ + q₁ + q₂ ≤ (unused.filter high).card at hhigh
  have hmid₀ : q₀ ≠ 0 → c - η / 2 < centralEntriesMean unused value ∧
      centralEntriesMean unused value < c + η / 2 := by
    intro _
    have h := abs_le.mp hmean
    constructor <;> linarith
  have hq₀ : q₀ < unused.card := by omega
  have hl₀ : q₀ ≤ (unused.filter low).card := by omega
  have hh₀ : q₀ ≤ (unused.filter high).card := by omega
  obtain ⟨A, hA, hAcard, hAcentral, hAerr, hApos, _, hAshift⟩ :=
    central_batch_select_and_update unused value hinj q₀ c η hη.le hq₀ hmid₀ hl₀ hh₀
  let S₁ := unused \ A
  have hc₁ : S₁.card + q₀ = unused.card := by
    simpa [S₁, hAcard] using Finset.card_sdiff_add_card_eq_card hA
  have hS₁ : S₁ ⊆ unused := Finset.sdiff_subset
  have hi₁ : Set.InjOn value (↑S₁ : Set α) := fun a ha b hb heq => hinj (hS₁ ha) (hS₁ hb) heq
  have hsize₁ : q₁ + q₂ + K ≤ S₁.card := by omega
  have hq₁ : q₁ < S₁.card := by omega
  have hl₁ : q₁ + q₂ ≤ (S₁.filter low).card := by
    exact central_stock_after_deletion unused A low (q₁ + q₂) (by rw [hAcard]; omega)
  have hh₁ : q₁ + q₂ ≤ (S₁.filter high).card := by
    exact central_stock_after_deletion unused A high (q₁ + q₂) (by rw [hAcard]; omega)
  have hden₁ : (13 : ℝ) ≤ (S₁.card : ℝ) := by exact_mod_cast (show 13 ≤ S₁.card by omega)
  have hshift₁ : |centralEntriesMean S₁ value - centralEntriesMean unused value| ≤ η / 13 :=
    hAshift.trans (div_le_div_of_nonneg_left hη.le (by norm_num) hden₁)
  have hmid₁ : q₁ ≠ 0 → c - η / 2 < centralEntriesMean S₁ value ∧
      centralEntriesMean S₁ value < c + η / 2 := by
    intro _
    have h₀ := abs_le.mp hmean
    have h₁ := abs_le.mp hshift₁
    constructor <;> linarith
  obtain ⟨B, hB, hBcard, hBcentral, hBerr, hBpos, _, hBshift⟩ :=
    central_batch_select_and_update S₁ value hi₁ q₁ c η hη.le hq₁ hmid₁
      (by change q₁ ≤ (S₁.filter low).card; omega)
      (by change q₁ ≤ (S₁.filter high).card; omega)
  let S₂ := S₁ \ B
  have hc₂ : S₂.card + q₁ = S₁.card := by
    simpa [S₂, hBcard] using Finset.card_sdiff_add_card_eq_card hB
  have hS₂ : S₂ ⊆ unused := Finset.sdiff_subset.trans hS₁
  have hi₂ : Set.InjOn value (↑S₂ : Set α) := fun a ha b hb heq => hinj (hS₂ ha) (hS₂ hb) heq
  have hsize₂ : q₂ + K ≤ S₂.card := by omega
  have hq₂ : q₂ < S₂.card := by omega
  have hl₂ : q₂ ≤ (S₂.filter low).card := by
    exact central_stock_after_deletion S₁ B low q₂ (by rw [hBcard]; omega)
  have hh₂ : q₂ ≤ (S₂.filter high).card := by
    exact central_stock_after_deletion S₁ B high q₂ (by rw [hBcard]; omega)
  have hden₂ : (13 : ℝ) ≤ (S₂.card : ℝ) := by exact_mod_cast (show 13 ≤ S₂.card by omega)
  have hshift₂ : |centralEntriesMean S₂ value - centralEntriesMean S₁ value| ≤ η / 13 :=
    hBshift.trans (div_le_div_of_nonneg_left hη.le (by norm_num) hden₂)
  have hmid₂ : q₂ ≠ 0 → c - η / 2 < centralEntriesMean S₂ value ∧
      centralEntriesMean S₂ value < c + η / 2 := by
    intro _
    have h₀ := abs_le.mp hmean
    have h₁ := abs_le.mp hshift₁
    have h₂ := abs_le.mp hshift₂
    constructor <;> linarith
  obtain ⟨C, hC, hCcard, hCcentral, hCerr, hCpos, _, _⟩ :=
    central_batch_select_and_update S₂ value hi₂ q₂ c η hη.le hq₂ hmid₂ hl₂ hh₂
  have hc₃ : (S₂ \ C).card + q₂ = S₂.card := by
    simpa [hCcard] using Finset.card_sdiff_add_card_eq_card hC
  refine ⟨A, B, C, hA, hB, hC, hAcard, hBcard, hCcard, ?_, hAerr, hBerr, hCerr, ?_⟩
  · intro a ha
    rcases Finset.mem_union.mp ha with hab | hc
    · rcases Finset.mem_union.mp hab with ha | hb
      · exact hAcentral a ha
      · exact hBcentral a hb
    · exact hCcentral a hc
  · change K ≤ (S₂ \ C).card
    omega

/-- CC1--CC2's original stock-size and diagonal-size hypotheses imply the
three-batch construction, with the common center selected exactly once. -/
theorem central_source_diagonal_batches {α : Type*} [DecidableEq α]
    (unused : Finset α) (value : α → ℝ) (hinj : Set.InjOn value (↑unused : Set α))
    (n q₁ q₂ : ℕ) (c η : ℝ) (hη : 0 < η) (hn : 20 ≤ n)
    (hN : 3 * n * n ≤ 4 * unused.card) (hq₁ : q₁ ≤ n - 1) (hq₂ : q₂ ≤ n - 1)
    (hmean : |centralEntriesMean unused value - c| ≤ η / 4)
    (hlow : 1 + q₁ + q₂ ≤
      (unused.filter (fun a => c - η < value a ∧ value a ≤ c - η / 2)).card)
    (hhigh : 1 + q₁ + q₂ ≤
      (unused.filter (fun a => c + η / 2 < value a ∧ value a ≤ c + η)).card) :
    ∃ A B C : Finset α,
      A ⊆ unused ∧ B ⊆ unused \ A ∧ C ⊆ (unused \ A) \ B ∧
      A.card = 1 ∧ B.card = q₁ ∧ C.card = q₂ ∧
      (∀ a ∈ A ∪ B ∪ C, |value a - c| ≤ η) ∧
      |(∑ a ∈ A, value a) - centralEntriesMean unused value| ≤ η ∧
      |(∑ a ∈ B, value a) - (q₁ : ℝ) * centralEntriesMean (unused \ A) value| ≤ η ∧
      |(∑ a ∈ C, value a) - (q₂ : ℝ) * centralEntriesMean ((unused \ A) \ B) value| ≤ η ∧
      n * n / 2 ≤ (((unused \ A) \ B) \ C).card := by
  have hreserve := central_source_reserve n unused.card q₁ q₂ hn hN hq₁ hq₂
  simpa using central_three_batches unused value hinj 1 q₁ q₂ (n * n / 2) c η
    hη hreserve.1 hreserve.2 hmean hlow hhigh

end
end Sude
