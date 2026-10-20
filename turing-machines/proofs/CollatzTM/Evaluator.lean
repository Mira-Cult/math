import CollatzTM.Core

namespace CollatzTM

/-- A reusable bridge for input evaluators.  These are explicit hypotheses,
not postulated properties of either supplied machine. -/
structure EvaluatorSpec (δ : S → Bool → Instr S) (F : Nat → Nat)
    (E : Nat → Int → Config S) : Prop where
  positive : ∀ n, 0 < n → 0 < F n
  live : ∀ n p, 0 < n → (E n p).state ≠ none
  one : ∀ p, Halts δ (E 1 p)
  advance : ∀ n p, 1 < n → ∃ t, 0 < t ∧ run δ t (E n p) = E (F n) (p+2)

def iter (F : Nat → Nat) : Nat → Nat → Nat
  | 0, n => n
  | k+1, n => iter F k (F n)

theorem evaluator_correct (δ : S → Bool → Instr S) (F : Nat → Nat)
    (E : Nat → Int → Config S) (spec : EvaluatorSpec δ F E)
    (n : Nat) (p : Int) (hn : 0 < n) :
    Halts δ (E n p) ↔ ∃ k, iter F k n = 1 := by
  constructor
  · rintro ⟨N, hN⟩
    have H : ∀ N n p, 0 < n → (run δ N (E n p)).state = none →
        ∃ k, iter F k n = 1 := by
      intro N
      induction N using Nat.strongRecOn with
      | ind N ih =>
        intro n p hn hN
        by_cases h1 : n = 1
        · exact ⟨0, h1⟩
        obtain ⟨t, ht, hrun⟩ := spec.advance n p (by omega)
        have htN : t ≤ N := by
          by_cases h : t ≤ N
          · exact h
          apply False.elim
          have hreach := reaches_no_early δ t _ _ hrun
            (spec.live (F n) (p+2) (spec.positive n hn))
          exact hreach.2 N (by omega) hN
        have hlast : (run δ (N-t) (E (F n) (p+2))).state = none := by
          have eq := run_add δ t (N-t) (E n p)
          rw [Nat.add_sub_of_le htN, hrun] at eq
          rw [← eq]
          exact hN
        obtain ⟨k, hk⟩ := ih (N-t) (by omega) (F n) (p+2)
          (spec.positive n hn) hlast
        exact ⟨k+1, hk⟩
    exact H N n p hn hN
  · rintro ⟨k, hk⟩
    induction k generalizing n p with
    | zero =>
      have h1 : n = 1 := hk
      rw [h1]
      exact spec.one p
    | succ k ih =>
      by_cases h1 : n = 1
      · rw [h1]; exact spec.one p
      obtain ⟨t, _, hrun⟩ := spec.advance n p (by omega)
      apply (halts_iff_of_run δ t _ _ hrun).2
      exact ih (F n) (p+2) (spec.positive n hn) hk

theorem evaluator_totality (δ : S → Bool → Instr S) (F : Nat → Nat)
    (E : Nat → Int → Config S) (spec : EvaluatorSpec δ F E) :
    (∀ n, 0 < n → Halts δ (E n 0)) ↔
    (∀ n, 0 < n → ∃ k, iter F k n = 1) := by
  constructor <;> intro h n hn
  · exact (evaluator_correct δ F E spec n 0 hn).1 (h n hn)
  · exact (evaluator_correct δ F E spec n 0 hn).2 (h n hn)

end CollatzTM
