import Mathlib.Tactic
import Mathlib.Data.List.Forall2

/-! Greedy balancing of supplied natural brackets around a real center.
No prime bracket or target existence is asserted. -/
namespace Sude
noncomputable section

/-- Starting at any discrepancy in `[-D,D]`, one may choose one supplied
endpoint for each label while retaining the bound and every supplied residue
class. `Forall₂` records the choice in the original order. -/
theorem t75_greedy_brackets_from {α : Type*} (xs : List α)
    (lo hi : α → ℕ) (h : ℕ) (y D start : ℝ) (_hD : 0 ≤ D)
    (hstart : -D ≤ start ∧ start ≤ D)
    (hbracket : ∀ x ∈ xs, y - D ≤ (lo x : ℝ) ∧ (lo x : ℝ) ≤ y ∧
      y ≤ (hi x : ℝ) ∧ (hi x : ℝ) ≤ y + D)
    (hclass : ∀ x ∈ xs, lo x % h = hi x % h) :
    ∃ values : List ℕ,
      List.Forall₂ (fun x v => v = lo x ∨ v = hi x) xs values ∧
      -D ≤ start + (values.sum : ℝ) - (xs.length : ℝ) * y ∧
      start + (values.sum : ℝ) - (xs.length : ℝ) * y ≤ D ∧
      values.sum % h = (xs.map lo).sum % h := by
  induction xs generalizing start with
  | nil =>
    exact ⟨[], List.Forall₂.nil, by simpa using hstart.1, by simpa using hstart.2, by simp⟩
  | cons x xs ih =>
    have hb := hbracket x (by simp)
    have hc := hclass x (by simp)
    have hv : ∃ v : ℕ, (v = lo x ∨ v = hi x) ∧
        (-D ≤ start + (v : ℝ) - y ∧ start + (v : ℝ) - y ≤ D) ∧
        v % h = lo x % h := by
      by_cases hs : 0 ≤ start
      · refine ⟨lo x, Or.inl rfl, ⟨?_, ?_⟩, rfl⟩ <;> linarith [hb.1, hb.2.1, hstart.2]
      · refine ⟨hi x, Or.inr rfl, ⟨?_, ?_⟩, hc.symm⟩ <;> linarith [hb.2.2.1, hb.2.2.2, hstart.1]
    obtain ⟨v, hv, hnew, hmod⟩ := hv
    obtain ⟨vs, hchoices, hlow, hhigh, hmods⟩ := ih (start + (v : ℝ) - y) hnew
      (fun z hz => hbracket z (by simp [hz])) (fun z hz => hclass z (by simp [hz]))
    refine ⟨v :: vs, List.Forall₂.cons hv hchoices, ?_, ?_, ?_⟩
    · simp only [List.sum_cons, Nat.cast_add, List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith
    · simp only [List.sum_cons, Nat.cast_add, List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith
    · simp only [List.sum_cons, List.map_cons]
      calc
        (v + vs.sum) % h = (v % h + vs.sum % h) % h := Nat.add_mod _ _ _
        _ = (lo x % h + (xs.map lo).sum % h) % h := by rw [hmod, hmods]
        _ = (lo x + (xs.map lo).sum) % h := (Nat.add_mod _ _ _).symm

/-- Zero initial discrepancy gives a balanced choice around `length * y`. -/
theorem t75_greedy_brackets {α : Type*} (xs : List α)
    (lo hi : α → ℕ) (h : ℕ) (y D : ℝ) (hD : 0 ≤ D)
    (hbracket : ∀ x ∈ xs, y - D ≤ (lo x : ℝ) ∧ (lo x : ℝ) ≤ y ∧
      y ≤ (hi x : ℝ) ∧ (hi x : ℝ) ≤ y + D)
    (hclass : ∀ x ∈ xs, lo x % h = hi x % h) :
    ∃ values : List ℕ,
      List.Forall₂ (fun x v => v = lo x ∨ v = hi x) xs values ∧
      |(values.sum : ℝ) - (xs.length : ℝ) * y| ≤ D ∧
      values.sum % h = (xs.map lo).sum % h := by
  obtain ⟨values, hchoice, hlo, hhi, hmod⟩ :=
    t75_greedy_brackets_from xs lo hi h y D 0 hD (by constructor <;> linarith) hbracket hclass
  refine ⟨values, hchoice, ?_, hmod⟩
  rw [abs_le]
  constructor <;> linarith

end
end Sude
