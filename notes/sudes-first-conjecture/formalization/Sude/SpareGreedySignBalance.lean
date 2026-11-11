import Mathlib.Tactic

/-! A finite signed-balancing lemma for potential spare-cell pairs.
It makes no assertion about physical cells, swaps, network flows, or a CY square. -/

namespace Sude
noncomputable section

/-- Given finitely many signed differences of magnitude at most `X`, signs can
be chosen so that their sum has magnitude at most `X`.  The empty set is
included. -/
theorem spare_greedy_sign_balance {α : Type*} [DecidableEq α]
    (s : Finset α) (d : α → ℝ) (X : ℝ) (hX : 0 ≤ X)
    (hd : ∀ i ∈ s, |d i| ≤ X) :
    ∃ choose : α → Bool,
      |∑ i ∈ s, if choose i then d i else -d i| ≤ X := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨fun _ => false, by simpa using hX⟩
  | @insert a s ha ih =>
    obtain ⟨choose, hchoose⟩ := ih (fun i hi => hd i (by simp [hi]))
    let total : ℝ := ∑ i ∈ s, if choose i then d i else -d i
    have ht : -X ≤ total ∧ total ≤ X := abs_le.mp hchoose
    have hx : -X ≤ d a ∧ d a ≤ X := abs_le.mp (hd a (by simp))
    have hstep : ∃ b : Bool, -X ≤ (if b then d a else -d a) + total ∧
        (if b then d a else -d a) + total ≤ X := by
      by_cases ht0 : 0 ≤ total
      · by_cases hd0 : 0 ≤ d a
        · exact ⟨false, by simp only [Bool.false_eq_true, ↓reduceIte]; linarith,
            by simp only [Bool.false_eq_true, ↓reduceIte]; linarith⟩
        · exact ⟨true, by simp only [↓reduceIte]; linarith,
            by simp only [↓reduceIte]; linarith⟩
      · by_cases hd0 : 0 ≤ d a
        · exact ⟨true, by simp only [↓reduceIte]; linarith,
            by simp only [↓reduceIte]; linarith⟩
        · exact ⟨false, by simp only [Bool.false_eq_true, ↓reduceIte]; linarith,
            by simp only [Bool.false_eq_true, ↓reduceIte]; linarith⟩
    obtain ⟨b, hlow, hhigh⟩ := hstep
    refine ⟨Function.update choose a b, ?_⟩
    rw [abs_le, Finset.sum_insert ha]
    have hsum : (∑ i ∈ s, if (Function.update choose a b) i then d i else -d i) = total := by
      apply Finset.sum_congr rfl
      intro i hi
      have hia : i ≠ a := by intro h; subst i; exact ha hi
      simp [Function.update, hia]
    rw [Function.update_self, hsum]
    exact ⟨hlow, hhigh⟩

/-- For two supplied values in `[0,X]` per label, independently exchanging
the two values balances the difference of their selected sums within `X`.
No distinctness assumption is needed for this numerical conclusion; physical
cell disjointness is a separate obligation. -/
theorem spare_greedy_pair_balance {α : Type*} [DecidableEq α]
    (s : Finset α) (a b : α → ℝ) (X : ℝ) (hX : 0 ≤ X)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ X)
    (hb : ∀ i ∈ s, 0 ≤ b i ∧ b i ≤ X) :
    ∃ choose : α → Bool,
      |∑ i ∈ s, ((if choose i then a i else b i) -
        (if choose i then b i else a i))| ≤ X := by
  have hd : ∀ i ∈ s, |a i - b i| ≤ X := by
    intro i hi
    rw [abs_le]
    obtain ⟨ha0, haX⟩ := ha i hi
    obtain ⟨hb0, hbX⟩ := hb i hi
    constructor <;> linarith
  obtain ⟨choose, hchoose⟩ := spare_greedy_sign_balance s (fun i => a i - b i) X hX hd
  refine ⟨choose, ?_⟩
  have heq : (∑ i ∈ s, ((if choose i then a i else b i) -
        (if choose i then b i else a i))) =
      ∑ i ∈ s, if choose i then a i - b i else -(a i - b i) := by
    apply Finset.sum_congr rfl
    intro i hi
    cases choose i <;> simp
  rw [heq]
  exact hchoose

end
end Sude
