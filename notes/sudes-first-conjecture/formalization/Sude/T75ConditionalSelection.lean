import Sude.T75GreedyBrackets
import Sude.T75StepGridResidual
import Mathlib.Data.Nat.ModEq

/-! Conditional finite target selection from supplied brackets and a supplied
step grid. No analytic supply, prime existence, or unconditional target
existence is asserted. -/
namespace Sude
noncomputable section

/-- Greedy free choices and a controlled subset realize the supplied exact
total when the supplied congruence and midpoint margin fit the step grid.
The free choices retain their given order and endpoints. -/
theorem t75_conditional_step_selection {α β : Type*} (xs : List α)
    (freeLo freeHi : α → ℕ) (S : Finset β) (low gap : β → ℕ)
    (h target : ℕ) (y D : ℝ) (hD : 0 ≤ D)
    (hbracket : ∀ x ∈ xs, y - D ≤ (freeLo x : ℝ) ∧ (freeLo x : ℝ) ≤ y ∧
      y ≤ (freeHi x : ℝ) ∧ (freeHi x : ℝ) ≤ y + D)
    (hclass : ∀ x ∈ xs, freeLo x % h = freeHi x % h)
    (hgrid : CompleteStepGrid S gap h (∑ i ∈ S, gap i))
    (hcong : ((∑ i ∈ S, low i) + (xs.map freeLo).sum) % h = target % h)
    (htotal : (target : ℝ) = ((xs.length : ℝ) + (S.card : ℝ)) * y)
    (hmargin : |((∑ i ∈ S, low i : ℕ) : ℝ) +
      ((∑ i ∈ S, gap i : ℕ) : ℝ) / 2 - (S.card : ℝ) * y| + D ≤
      ((∑ i ∈ S, gap i : ℕ) : ℝ) / 2) :
    ∃ values : List ℕ, ∃ chosen : Finset β,
      List.Forall₂ (fun x v => v = freeLo x ∨ v = freeHi x) xs values ∧
      values.length = xs.length ∧
      |(values.sum : ℝ) - (xs.length : ℝ) * y| ≤ D ∧
      values.sum % h = (xs.map freeLo).sum % h ∧ chosen ⊆ S ∧
      target = values.sum + (∑ i ∈ S, low i) + ∑ i ∈ chosen, gap i := by
  obtain ⟨values, hchoice, hbalance, hmod⟩ :=
    t75_greedy_brackets xs freeLo freeHi h y D hD hbracket hclass
  have hb := abs_le.mp hbalance
  have hm := abs_le.mp (show |((∑ i ∈ S, low i : ℕ) : ℝ) +
      ((∑ i ∈ S, gap i : ℕ) : ℝ) / 2 - (S.card : ℝ) * y| ≤
      ((∑ i ∈ S, gap i : ℕ) : ℝ) / 2 - D by linarith)
  have hlo : values.sum + (∑ i ∈ S, low i) ≤ target := by
    have hr : (values.sum : ℝ) + ((∑ i ∈ S, low i : ℕ) : ℝ) ≤ target := by
      nlinarith [hb.1, hm.2, htotal]
    exact_mod_cast hr
  have hhi : target ≤ values.sum + (∑ i ∈ S, low i) + ∑ i ∈ S, gap i := by
    have hr : (target : ℝ) ≤ (values.sum : ℝ) + ((∑ i ∈ S, low i : ℕ) : ℝ) +
        ((∑ i ∈ S, gap i : ℕ) : ℝ) := by
      nlinarith [hb.2, hm.1, htotal]
    exact_mod_cast hr
  have hmodEq : values.sum + (∑ i ∈ S, low i) ≡ target [MOD h] := by
    show (values.sum + ∑ i ∈ S, low i) % h = target % h
    calc
      _ = ((∑ i ∈ S, low i) + values.sum) % h := by rw [add_comm]
      _ = ((∑ i ∈ S, low i) % h + values.sum % h) % h := Nat.add_mod _ _ _
      _ = ((∑ i ∈ S, low i) % h + (xs.map freeLo).sum % h) % h := by rw [hmod]
      _ = ((∑ i ∈ S, low i) + (xs.map freeLo).sum) % h := (Nat.add_mod _ _ _).symm
      _ = target % h := hcong
  have hdiv : h ∣ target - (values.sum + ∑ i ∈ S, low i) :=
    (Nat.modEq_iff_dvd' hlo).mp hmodEq
  obtain ⟨chosen, hsub, heq⟩ := t75_step_grid_exact_residual S gap h
    (∑ i ∈ S, gap i) values.sum (∑ i ∈ S, low i) target hgrid hlo hhi hdiv
  exact ⟨values, chosen, hchoice, hchoice.length_eq.symm, hbalance, hmod, hsub, heq⟩

end
end Sude
