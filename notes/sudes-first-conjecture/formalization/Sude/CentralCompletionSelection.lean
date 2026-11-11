import Sude.CentralThreeBatches
import Sude.CentralAggregate

/-! Three actual diagonal batches with the combined CC10 error bound. -/
namespace Sude
noncomputable section

/-- The CC1--CC2 stock hypotheses produce three disjoint batches, selecting
the center once, with both their individual current-mean errors and the
combined original-mean error bounded. This does not assign cells or fill the
regular factor. -/
theorem central_source_batches_with_total_error {α : Type*} [DecidableEq α]
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
      n * n / 2 ≤ (((unused \ A) \ B) \ C).card ∧
      |(∑ a ∈ A ∪ B ∪ C, value a) -
        ((1 + q₁ + q₂ : ℕ) : ℝ) * centralEntriesMean unused value| ≤ 3 * η := by
  classical
  obtain ⟨A, B, C, hA, hB, hC, hcA, hcB, hcC, hcentral, he₀, he₁, he₂, hremaining⟩ :=
    central_source_diagonal_batches unused value hinj n q₁ q₂ c η hη hn hN hq₁ hq₂ hmean hlow hhigh
  have hreserve := (central_source_reserve n unused.card q₁ q₂ hn hN hq₁ hq₂).1
  have hpos : 0 < (((unused \ A) \ B) \ C).card := by omega
  have he₀' : |(∑ a ∈ A, value a) - (A.card : ℝ) * centralEntriesMean unused value| ≤ η := by
    simpa [hcA] using he₀
  have he₁' : |(∑ a ∈ B, value a) - (B.card : ℝ) * centralEntriesMean (unused \ A) value| ≤ η := by
    simpa [hcB] using he₁
  have he₂' : |(∑ a ∈ C, value a) - (C.card : ℝ) * centralEntriesMean ((unused \ A) \ B) value| ≤ η := by
    simpa [hcC] using he₂
  have htotal := central_actual_three_batch_error unused A B C value η hA hB hC hpos hη.le he₀' he₁' he₂'
  have hab : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_sdiff.mp (hB hb)).2 ha
  have habc : Disjoint (A ∪ B) C := by
    apply Finset.disjoint_left.mpr
    intro a hab' hc
    have hc' := Finset.mem_sdiff.mp (hC hc)
    rcases Finset.mem_union.mp hab' with ha | hb
    · exact (Finset.mem_sdiff.mp hc'.1).2 ha
    · exact hc'.2 hb
  have hsum : (∑ a ∈ A ∪ B ∪ C, value a) =
      (∑ a ∈ A, value a) + (∑ a ∈ B, value a) + (∑ a ∈ C, value a) := by
    rw [Finset.sum_union habc, Finset.sum_union hab]
  refine ⟨A, B, C, hA, hB, hC, hcA, hcB, hcC, hcentral, he₀, he₁, he₂, hremaining, ?_⟩
  rw [hsum]
  simpa [hcA, hcB, hcC] using htotal

end
end Sude
