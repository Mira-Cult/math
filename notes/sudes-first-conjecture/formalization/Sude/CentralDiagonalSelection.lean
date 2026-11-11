import Sude.CentralCompletionSelection
import Sude.CentralActualDiagonal

/-! Compose CC2's actual selection and CC3's two diagonal error bounds. -/
namespace Sude
noncomputable section

/-- The source's stock hypotheses give three disjoint central batches with
the common center selected once, CC10's combined error, and both CC11
labelled diagonal errors. Cell placement and the off-diagonal factor are
separate construction obligations. -/
theorem central_source_batches_with_diagonal_errors {α : Type*} [DecidableEq α]
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
      n * n / 2 ≤ (((unused \ A) \ B) \ C).card ∧
      |(∑ a ∈ A ∪ B ∪ C, value a) -
        ((1 + q₁ + q₂ : ℕ) : ℝ) * centralEntriesMean unused value| ≤ 3 * η ∧
      |(∑ a ∈ A ∪ B, value a) -
        ((1 + q₁ : ℕ) : ℝ) * centralEntriesMean unused value| ≤ 2 * η ∧
      |(∑ a ∈ A ∪ C, value a) -
        ((1 + q₂ : ℕ) : ℝ) * centralEntriesMean unused value| ≤ (201 / 100) * η := by
  obtain ⟨A, B, C, hA, hB, hC, hcA, hcB, hcC, hcentral, he₀, he₁, he₂, hleft, htotal⟩ :=
    central_source_batches_with_total_error unused value hinj n q₁ q₂ c η hη hn hN hq₁ hq₂
      hmean hlow hhigh
  have hdiags := central_actual_diagonal_errors unused A B C value n q₁ q₂ η
    hn hN hq₁ hq₂ hη.le hA hB hC hcA hcB hcC he₀ he₁ he₂
  exact ⟨A, B, C, hA, hB, hC, hcA, hcB, hcC, hcentral, hleft, htotal, hdiags.1, hdiags.2⟩

end
end Sude
