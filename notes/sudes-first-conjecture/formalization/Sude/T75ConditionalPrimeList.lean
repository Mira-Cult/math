import Sude.T75ConditionalSelection

/-! A concrete target list from conditional finite selection and supplied
prime endpoints. This does not supply the endpoints, grid, or numeric gates. -/
namespace Sude
noncomputable section

/-- Ordered choices from supplied prime endpoints remain prime. -/
theorem t75_bracket_choices_prime {α : Type*} {xs : List α} {values : List ℕ}
    (lo hi : α → ℕ)
    (hchoice : List.Forall₂ (fun x v => v = lo x ∨ v = hi x) xs values)
    (hprime : ∀ x ∈ xs, Nat.Prime (lo x) ∧ Nat.Prime (hi x)) :
    ∀ v ∈ values, Nat.Prime v := by
  induction hchoice with
  | nil => simp
  | @cons x v xs vs hhead htail ih =>
    intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · obtain ⟨hl, hh⟩ := hprime x (by simp)
      rcases hhead with rfl | rfl <;> assumption
    · exact ih (fun x hx => hprime x (by simp [hx])) z hz

/-- The supplied prime brackets and prime controlled endpoint pairs yield an
actual ordered list of the stated length and exact total, assuming the grid,
congruence, exact center and midpoint margin. Repeated targets are allowed. -/
theorem t75_conditional_prime_target_list {α β : Type*} [DecidableEq β]
    (xs : List α) (freeLo freeHi : α → ℕ) (S : Finset β) (low gap : β → ℕ)
    (h target : ℕ) (y D : ℝ) (hD : 0 ≤ D)
    (hbracket : ∀ x ∈ xs, y - D ≤ (freeLo x : ℝ) ∧ (freeLo x : ℝ) ≤ y ∧
      y ≤ (freeHi x : ℝ) ∧ (freeHi x : ℝ) ≤ y + D)
    (hclass : ∀ x ∈ xs, freeLo x % h = freeHi x % h)
    (hfreePrime : ∀ x ∈ xs, Nat.Prime (freeLo x) ∧ Nat.Prime (freeHi x))
    (hcontrolledPrime : ∀ i ∈ S, Nat.Prime (low i) ∧ Nat.Prime (low i + gap i))
    (hgrid : CompleteStepGrid S gap h (∑ i ∈ S, gap i))
    (hcong : ((∑ i ∈ S, low i) + (xs.map freeLo).sum) % h = target % h)
    (htotal : (target : ℝ) = ((xs.length : ℝ) + (S.card : ℝ)) * y)
    (hmargin : |((∑ i ∈ S, low i : ℕ) : ℝ) +
      ((∑ i ∈ S, gap i : ℕ) : ℝ) / 2 - (S.card : ℝ) * y| + D ≤
      ((∑ i ∈ S, gap i : ℕ) : ℝ) / 2) :
    ∃ values : List ℕ, ∃ chosen : Finset β,
      chosen ⊆ S ∧ List.Forall₂ (fun x v => v = freeLo x ∨ v = freeHi x) xs values ∧
      let controlled := S.toList.map (fun i => if i ∈ chosen then low i + gap i else low i)
      let targets := values ++ controlled
      targets.length = xs.length + S.card ∧ targets.sum = target ∧
      (∀ v ∈ targets, Nat.Prime v) := by
  obtain ⟨values, chosen, hchoice, hlength, hbalance, hmod, hsub, heq⟩ :=
    t75_conditional_step_selection xs freeLo freeHi S low gap h target y D hD
      hbracket hclass hgrid hcong htotal hmargin
  have hvaluesPrime := t75_bracket_choices_prime freeLo freeHi hchoice hfreePrime
  have hsum : (∑ i ∈ S, (if i ∈ chosen then low i + gap i else low i)) =
      (∑ i ∈ S, low i) + ∑ i ∈ chosen, gap i := by
    calc
      _ = ∑ i ∈ S, (low i + if i ∈ chosen then gap i else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        split <;> simp_all
      _ = (∑ i ∈ S, low i) + ∑ i ∈ S, (if i ∈ chosen then gap i else 0) := Finset.sum_add_distrib
      _ = _ := by rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
  refine ⟨values, chosen, hsub, hchoice, ?_, ?_, ?_⟩
  · simp [hlength]
  · simp only [List.sum_append, Finset.sum_map_toList, hsum]
    omega
  · intro v hv
    simp only [List.mem_append, List.mem_map, Finset.mem_toList] at hv
    rcases hv with hv | ⟨i, hi, rfl⟩
    · exact hvaluesPrime v hv
    · obtain ⟨hl, hu⟩ := hcontrolledPrime i hi
      split <;> assumption

end
end Sude
