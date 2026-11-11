import Sude.T75ConditionalPrimeList
import Sude.FWTargetDemandBudget

/-! Endpoint windows for the same conditional T75 list and its indexed prime
targets. Endpoint supply, window, reference estimates and budget are explicit. -/
namespace Sude
noncomputable section

/-- Every choice from supplied free brackets stays in their common window. -/
theorem t75_bracket_choices_window {α : Type*} {xs : List α} {values : List ℕ}
    (lo hi : α → ℕ) (y D : ℝ)
    (hchoice : List.Forall₂ (fun x v => v = lo x ∨ v = hi x) xs values)
    (hbracket : ∀ x ∈ xs, y - D ≤ (lo x : ℝ) ∧ (lo x : ℝ) ≤ y ∧
      y ≤ (hi x : ℝ) ∧ (hi x : ℝ) ≤ y + D) :
    ∀ v ∈ values, y - D ≤ (v : ℝ) ∧ (v : ℝ) ≤ y + D := by
  induction hchoice with
  | nil => simp
  | @cons x v xs vs hhead htail ih =>
    intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · obtain ⟨hl, hl', hh, hh'⟩ := hbracket x (by simp)
      rcases hhead with rfl | rfl <;> constructor <;> linarith
    · exact ih (fun x hx => hbracket x (by simp [hx])) z hz

/-- The selected T75 list is the list indexed by the resulting prime vector.
The controlled endpoints must each fit the window; exact total, common center,
and all selection premises remain explicit. -/
theorem t75_conditional_indexed_prime_targets {α β : Type*} [DecidableEq β]
    (xs : List α) (freeLo freeHi : α → ℕ) (S : Finset β) (low gap : β → ℕ)
    (h target n : ℕ) (y D : ℝ) (hD : 0 ≤ D)
    (hbracket : ∀ x ∈ xs, y - D ≤ (freeLo x : ℝ) ∧ (freeLo x : ℝ) ≤ y ∧
      y ≤ (freeHi x : ℝ) ∧ (freeHi x : ℝ) ≤ y + D)
    (hclass : ∀ x ∈ xs, freeLo x % h = freeHi x % h)
    (hfreePrime : ∀ x ∈ xs, Nat.Prime (freeLo x) ∧ Nat.Prime (freeHi x))
    (hcontrolledPrime : ∀ i ∈ S, Nat.Prime (low i) ∧ Nat.Prime (low i + gap i))
    (hwindow : ∀ i ∈ S, y - D ≤ (low i : ℝ) ∧ ((low i + gap i : ℕ) : ℝ) ≤ y + D)
    (hgrid : CompleteStepGrid S gap h (∑ i ∈ S, gap i))
    (hcong : ((∑ i ∈ S, low i) + (xs.map freeLo).sum) % h = target % h)
    (htotal : (target : ℝ) = ((xs.length : ℝ) + (S.card : ℝ)) * y)
    (hmargin : |((∑ i ∈ S, low i : ℕ) : ℝ) +
      ((∑ i ∈ S, gap i : ℕ) : ℝ) / 2 - (S.card : ℝ) * y| + D ≤
      ((∑ i ∈ S, gap i : ℕ) : ℝ) / 2)
    (hn : xs.length + S.card = n) (habove : (2 : ℝ) < y - D) :
    ∃ values : List ℕ, ∃ chosen : Finset β,
      chosen ⊆ S ∧ List.Forall₂ (fun x v => v = freeLo x ∨ v = freeHi x) xs values ∧
      let targets := values ++ S.toList.map (fun i => if i ∈ chosen then low i + gap i else low i)
      ∃ hlen : targets.length = n, ∃ f : Fin n → ℕ,
        (∀ i, f i = targets.get ((finCongr hlen.symm) i)) ∧
        (∑ i, f i) = target ∧
        (∀ i, Nat.Prime (f i) ∧ Odd (f i) ∧ |(f i : ℝ) - y| ≤ D) := by
  obtain ⟨values, chosen, hsub, hchoice, hlength, hsum, hprime⟩ :=
    t75_conditional_prime_target_list xs freeLo freeHi S low gap h target y D hD
      hbracket hclass hfreePrime hcontrolledPrime hgrid hcong htotal hmargin
  let targets := values ++ S.toList.map (fun i => if i ∈ chosen then low i + gap i else low i)
  have hlen : targets.length = n := hlength.trans hn
  let e : Fin n ≃ Fin targets.length := finCongr hlen.symm
  let f : Fin n → ℕ := fun i => targets.get (e i)
  have hwin : ∀ v ∈ targets, y - D ≤ (v : ℝ) ∧ (v : ℝ) ≤ y + D := by
    intro v hv
    simp only [targets, List.mem_append, List.mem_map, Finset.mem_toList] at hv
    rcases hv with hv | ⟨i, hi, rfl⟩
    · exact t75_bracket_choices_window freeLo freeHi y D hchoice hbracket v hv
    · obtain ⟨hl, hu⟩ := hwindow i hi
      have hle : (low i : ℝ) ≤ ((low i + gap i : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_right (low i) (gap i))
      split <;> constructor <;> linarith
  have hgets : (∑ i : Fin targets.length, targets.get i) = targets.sum := by
    rw [← List.sum_ofFn, List.ofFn_get]
  refine ⟨values, chosen, hsub, hchoice, hlen, f, ?_, ?_, ?_⟩
  · intro i; rfl
  · calc
      (∑ i, f i) = ∑ i : Fin targets.length, targets.get i := Equiv.sum_comp e targets.get
      _ = targets.sum := hgets
      _ = target := hsum
  · intro i
    have hmem : f i ∈ targets := List.get_mem _ _
    have hp : Nat.Prime (f i) := hprime _ hmem
    have hw := hwin _ hmem
    have hne : f i ≠ 2 := by intro heq; rw [heq] at hw; norm_num at hw; linarith
    refine ⟨hp, Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left hne), ?_⟩
    apply abs_le.mpr
    constructor <;> linarith

end
end Sude
