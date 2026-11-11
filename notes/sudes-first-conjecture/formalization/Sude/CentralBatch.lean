import Sude.CentralStock

/-! One actual central batch, including its exact effect on the unused mean. -/
namespace Sude
noncomputable section

/-- Select one batch from the two actual outer stocks, delete it, and bound
the resulting mean shift. For a zero-size batch the center condition is not
needed. The premise `q < unused.card` ensures a positive remaining count. -/
theorem central_batch_select_and_update {α : Type*} [DecidableEq α]
    (unused : Finset α) (value : α → ℝ) (hinj : Set.InjOn value (↑unused : Set α))
    (q : ℕ) (c η : ℝ) (hη : 0 ≤ η) (hremaining : q < unused.card)
    (hmid : q ≠ 0 → c - η / 2 < centralEntriesMean unused value ∧
      centralEntriesMean unused value < c + η / 2)
    (hlow : q ≤ (unused.filter (fun a => c - η < value a ∧ value a ≤ c - η / 2)).card)
    (hhigh : q ≤ (unused.filter (fun a => c + η / 2 < value a ∧ value a ≤ c + η)).card) :
    ∃ T : Finset α, T ⊆ unused ∧ T.card = q ∧
      (∀ a ∈ T, |value a - c| ≤ η) ∧
      |(∑ a ∈ T, value a) - (q : ℝ) * centralEntriesMean unused value| ≤ η ∧
      0 < (unused \ T).card ∧
      centralEntriesMean (unused \ T) value = centralEntriesMean unused value -
        ((∑ a ∈ T, value a) - (q : ℝ) * centralEntriesMean unused value) /
          ((unused \ T).card : ℝ) ∧
      |centralEntriesMean (unused \ T) value - centralEntriesMean unused value| ≤
        η / ((unused \ T).card : ℝ) := by
  obtain ⟨T, hT, hcard, hcentral, herr⟩ :=
    central_unused_entries_select unused value hinj q c η (centralEntriesMean unused value)
      hη hmid hlow hhigh
  have hc := Finset.card_sdiff_add_card_eq_card hT
  have hpos : 0 < (unused \ T).card := by omega
  have hmean := central_entries_actual_mean_update unused T value hT hpos
  rw [hcard] at hmean
  have hden : (0 : ℝ) < ((unused \ T).card : ℝ) := by exact_mod_cast hpos
  refine ⟨T, hT, hcard, hcentral, herr, hpos, hmean, ?_⟩
  rw [hmean]
  have heq : centralEntriesMean unused value -
        ((∑ a ∈ T, value a) - (q : ℝ) * centralEntriesMean unused value) /
          ((unused \ T).card : ℝ) - centralEntriesMean unused value =
      -(((∑ a ∈ T, value a) - (q : ℝ) * centralEntriesMean unused value) /
          ((unused \ T).card : ℝ)) := by ring
  rw [heq, abs_neg, abs_div, abs_of_pos hden]
  exact div_le_div_of_nonneg_right herr (le_of_lt hden)

end
end Sude
