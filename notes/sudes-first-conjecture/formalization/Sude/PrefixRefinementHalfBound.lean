import Sude.PrefixHistoryKeyRefinement
import Sude.PrefixBalancedSplitDepth

/-! Balanced half-size bounds for history-refined slot groups. -/
namespace Sude
noncomputable section

/-- Each child of a balanced slot group has at most the larger half of the
parent size. This includes empty and singleton parents. -/
theorem prefix_refined_child_le_larger_half {S G : Type*} [DecidableEq S]
    [DecidableEq G] (slots : Finset S) (gs : S → G) (chosen : Finset S)
    (g : G)
    (hchosen : ((slots.filter (fun s => gs s = g)).filter (fun s => s ∈ chosen)).card =
      (slots.filter (fun s => gs s = g)).card / 2) :
    ∀ b : Bool, (slots.filter (fun s => (gs s, decide (s ∈ chosen)) = (g,b))).card ≤
      (slots.filter (fun s => gs s = g)).card - (slots.filter (fun s => gs s = g)).card / 2 := by
  classical
  let q := (slots.filter (fun s => gs s = g)).card
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := slots.filter (fun s => gs s = g)) (fun s => s ∈ chosen)
  have hm := Nat.mod_lt q (by norm_num : 0 < 2)
  have hd := Nat.mod_add_div q 2
  intro b
  cases b with
  | false =>
    have hchild : ((slots.filter (fun s => gs s = g)).filter (fun s => s ∉ chosen)).card ≤
        q - q / 2 := by omega
    simpa [Finset.filter_filter, q] using hchild
  | true =>
    have hchild : ((slots.filter (fun s => gs s = g)).filter (fun s => s ∈ chosen)).card ≤
        q - q / 2 := by omega
    simpa [Finset.filter_filter, q] using hchild

/-- History recoding transfers the balanced half-size bound to every child
key, including keys not attained by any slot. -/
theorem prefix_history_refined_half_bound {S G : Type*} [DecidableEq S]
    [DecidableEq G] (slots : Finset S) (gs : S → G × List Bool)
    (chosen : Finset S) (B : ℕ)
    (hchosen : ∀ g, ((slots.filter (fun s => gs s = g)).filter (fun s => s ∈ chosen)).card =
      (slots.filter (fun s => gs s = g)).card / 2)
    (hsize : ∀ g, (slots.filter (fun s => gs s = g)).card ≤ B) :
    ∀ k, (slots.filter (fun s => prefixHistoryChild (gs s, decide (s ∈ chosen)) = k)).card ≤
      B - B / 2 := by
  classical
  intro k
  by_cases hk : ∃ p, prefixHistoryChild p = k
  · obtain ⟨⟨g,b⟩, rfl⟩ := hk
    rw [prefix_injective_recode_fiber slots
      (fun s => (gs s, decide (s ∈ chosen))) prefixHistoryChild
      prefix_history_child_injective (g,b)]
    have h := prefix_refined_child_le_larger_half slots gs chosen g (hchosen g) b
    have hb := hsize g
    have hmono : (slots.filter (fun s => gs s = g)).card -
      (slots.filter (fun s => gs s = g)).card / 2 ≤ B - B / 2 := by omega
    exact h.trans hmono
  · have h : slots.filter (fun s => prefixHistoryChild (gs s, decide (s ∈ chosen)) = k) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro s hs he
      exact hk ⟨(gs s, decide (s ∈ chosen)), he⟩
    simp [h]

/-- If parent fibers have the iterated balanced bound at depth k, their
history-refined children have the bound at depth k+1. -/
theorem prefix_history_refined_balanced_max {S G : Type*} [DecidableEq S]
    [DecidableEq G] (slots : Finset S) (gs : S → G × List Bool)
    (chosen : Finset S) (Q k : ℕ)
    (hchosen : ∀ g, ((slots.filter (fun s => gs s = g)).filter (fun s => s ∈ chosen)).card =
      (slots.filter (fun s => gs s = g)).card / 2)
    (hsize : ∀ g, (slots.filter (fun s => gs s = g)).card ≤ prefixBalancedMax Q k) :
    ∀ p, (slots.filter (fun s => prefixHistoryChild (gs s, decide (s ∈ chosen)) = p)).card ≤
      prefixBalancedMax Q (k + 1) := by
  have hrec : ∀ k Q, prefixBalancedMax Q (k + 1) =
      prefixBalancedMax Q k - prefixBalancedMax Q k / 2 := by
    intro j
    induction j with
    | zero => intro n; rfl
    | succ j ih =>
      intro n
      simpa [prefixBalancedMax] using ih (n - n / 2)
  have h := prefix_history_refined_half_bound slots gs chosen (prefixBalancedMax Q k) hchosen hsize
  simpa only [hrec] using h


end
end Sude
