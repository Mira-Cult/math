import Sude.PrefixOneLevelRounding
import Sude.PrefixBinarySelection
import Sude.PrefixRoundingInitialFibers
import Sude.PrefixRoundingCoefficientBound

/-! DP2: one joint split of every finite slot group. Recursive splitting,
physical slot assignment and complete line bounds are separate. -/
namespace Sude
noncomputable section

/-- Simultaneously select exactly the requested number of labelled slots from
each group, with one `10*C` discrepancy per line across all groups. The group
widths and line weights are fixed throughout the selection. -/
theorem prefix_simultaneous_split {S G L : Type*}
    [DecidableEq S] [DecidableEq G] [DecidableEq L]
    (U : Finset S) (group : S → G) (m : G → ℕ)
    (lines : Finset L) (w : L → S → ℝ) (delta : G → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hm : ∀ g, m g ≤ (U.filter (fun s => group s = g)).card)
    (hw : ∀ l ∈ lines, ∀ s ∈ U, 0 ≤ w l s)
    (hweight : ∀ s ∈ U, (∑ l ∈ lines, w l s) ≤ 5)
    (hdelta : ∀ s ∈ U, 0 ≤ delta (group s) ∧ delta (group s) ≤ C) :
    ∃ T : Finset S, T ⊆ U ∧
      (∀ g ∈ U.image group, (T.filter (fun s => group s = g)).card = m g) ∧
      (∀ l ∈ lines,
        |∑ s ∈ U, (w l s * delta (group s)) *
          ((if s ∈ T then (1 : ℝ) else 0) - prefixGroupInitial U group m s)| ≤ 10 * C) := by
  classical
  obtain ⟨hnonneg, hcol⟩ := prefix_rounding_coefficient_bound U lines group w delta C hw hweight hdelta
  have hbox : ∀ s ∈ U, 0 ≤ prefixGroupInitial U group m s ∧ prefixGroupInitial U group m s ≤ 1 :=
    fun s hs => prefix_group_initial_box U group m hm s hs
  have hint : ∀ g, ∃ z : ℤ,
      (∑ s ∈ U, if group s = g then prefixGroupInitial U group m s else 0) = z := by
    intro g
    refine ⟨m g, ?_⟩
    simpa using prefix_group_initial_sum U group m hm g
  obtain ⟨y, hy, hfreeze, hsum, hline⟩ := prefix_one_level_rounding U group lines
    (fun l s => w l s * delta (group s)) C hC hnonneg hcol
    (prefixGroupInitial U group m) hbox hint
  have hgroup : ∀ g ∈ U.image group,
      (∑ s ∈ U, if group s = g then y s else 0) = (m g : ℝ) := by
    intro g hg
    rw [hsum g]
    exact prefix_group_initial_sum U group m hm g
  obtain ⟨T, hTU, hyT, hcard⟩ := prefix_binary_vector_to_selection U group m y hy hgroup
  refine ⟨T, hTU, hcard, ?_⟩
  intro l hl
  have h := hline l hl
  apply le_trans _ h
  apply le_of_eq
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [hyT s hs]

end
end Sude
