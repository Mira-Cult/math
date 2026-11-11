import Sude.PrefixHistoryKeyRefinement

/-! Arbitrary-cap bounds for balanced history refinement. This supplies only
fiber-size arithmetic; no rounded selection or recursion is constructed. -/
namespace Sude
noncomputable section

/-- If the selected part is half the parent rounded down and the parent has
at most `R` entries, either refined child has at most `R - R/2` entries. -/
theorem prefix_refined_balanced_child_cap {S G : Type*} [DecidableEq S]
    [DecidableEq G] (slots : Finset S) (gs : S → G) (chosen : Finset S)
    (g : G) (R : ℕ)
    (hchosen : ((slots.filter (fun s => gs s = g)).filter (fun s => s ∈ chosen)).card =
      (slots.filter (fun s => gs s = g)).card / 2)
    (hsize : (slots.filter (fun s => gs s = g)).card ≤ R) :
    ∀ b : Bool, (slots.filter (fun s => (gs s, decide (s ∈ chosen)) = (g,b))).card ≤ R - R / 2 := by
  classical
  let q := (slots.filter (fun s => gs s = g)).card
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := slots.filter (fun s => gs s = g)) (fun s => s ∈ chosen)
  have hqcap : q - q / 2 ≤ R - R / 2 := by omega
  have hqhalf : q / 2 ≤ q - q / 2 := by omega
  intro b
  cases b with
  | false =>
    have hchild : ((slots.filter (fun s => gs s = g)).filter (fun s => s ∉ chosen)).card ≤ R - R / 2 := by
      omega
    simpa [Finset.filter_filter] using hchild
  | true =>
    have hchild : ((slots.filter (fun s => gs s = g)).filter (fun s => s ∈ chosen)).card ≤ R - R / 2 := by
      omega
    simpa [Finset.filter_filter] using hchild

/-- Appending a Boolean split to history keys preserves the same arbitrary
balanced capacity for every recoded key, including keys outside the image. -/
theorem prefix_history_refined_balanced_cap {S G : Type*} [DecidableEq S]
    [DecidableEq G] (slots : Finset S) (gs : S → G × List Bool)
    (chosen : Finset S) (R : ℕ)
    (hchosen : ∀ g, ((slots.filter (fun s => gs s = g)).filter (fun s => s ∈ chosen)).card =
      (slots.filter (fun s => gs s = g)).card / 2)
    (hsize : ∀ g, (slots.filter (fun s => gs s = g)).card ≤ R) :
    ∀ k, (slots.filter (fun s => prefixHistoryChild (gs s, decide (s ∈ chosen)) = k)).card ≤ R - R / 2 := by
  classical
  intro k
  by_cases hk : ∃ p, prefixHistoryChild p = k
  · obtain ⟨⟨g,b⟩, rfl⟩ := hk
    rw [prefix_injective_recode_fiber slots
      (fun s => (gs s, decide (s ∈ chosen))) prefixHistoryChild
      prefix_history_child_injective (g,b)]
    exact prefix_refined_balanced_child_cap slots gs chosen g R (hchosen g) (hsize g) b
  · have h : slots.filter (fun s => prefixHistoryChild (gs s, decide (s ∈ chosen)) = k) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro s hs he
      exact hk ⟨(gs s, decide (s ∈ chosen)), he⟩
    simp [h]

end
end Sude
