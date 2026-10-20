import CollatzTM.Evaluator
import CollatzTM.Search
import CollatzTM.ArithmeticBridge

namespace CollatzTM

/-- The machine framework iterates from the input; the arithmetic files
    iterate from the output. These conventions define the same function. -/
theorem iter_eq_iterate (f : Nat → Nat) (k n : Nat) :
    iter f k n = Arithmetic.iterate f k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    change iter f k (f n) = Arithmetic.iterate f (k+1) n
    rw [ih,Arithmetic.iterate_succ']

theorem iter_shortcut_eq_sit (k n : Nat) :
    iter Arithmetic.shortcut k n = Arithmetic.sit k n := iter_eq_iterate _ _ _

/-- Ordinary Collatz correctness after a concrete evaluator supplies every
    field of `EvaluatorSpec`. No table-specific macro is assumed implicitly. -/
theorem evaluator_ordinary_correct (δ : S → Bool → Instr S)
    (E : Nat → Int → Config S) (spec : EvaluatorSpec δ Arithmetic.shortcut E)
    (n : Nat) (p : Int) (hn : 0<n) :
    Halts δ (E n p) ↔ ∃ k, Arithmetic.uit k n=1 := by
  apply (evaluator_correct δ Arithmetic.shortcut E spec n p hn).trans
  apply Iff.trans ?_ (Arithmetic.reaches_one_iff n)
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k,by rw [← iter_shortcut_eq_sit]; exact hk⟩
  · rintro ⟨k,hk⟩
    exact ⟨k,by rw [iter_shortcut_eq_sit]; exact hk⟩

/-- The universal positive-input evaluator statement is equivalent to the
    ordinary Collatz conjecture once its explicit macro interface is proved. -/
theorem evaluator_totality_ordinary (δ : S → Bool → Instr S)
    (E : Nat → Int → Config S) (spec : EvaluatorSpec δ Arithmetic.shortcut E) :
    (∀ n, 0<n → Halts δ (E n 0)) ↔
    (∀ n, 0<n → ∃ k, Arithmetic.uit k n=1) := by
  constructor
  · intro h n hn
    exact (evaluator_ordinary_correct δ E spec n 0 hn).mp (h n hn)
  · intro h n hn
    exact (evaluator_ordinary_correct δ E spec n 0 hn).mpr (h n hn)

/-- Ordinary cycle correctness after a concrete cycle detector supplies every
    field of `CycleMachineSpec`. Divergent nonperiodic orbits are outside this predicate. -/
theorem cycle_machine_ordinary_correct (δ : S → Bool → Instr S)
    (start : Config S) (C : Nat → Nat → Config S)
    (spec : CycleMachineSpec δ start C) :
    Halts δ start ↔ Arithmetic.OrdinaryCounter := by
  exact (cycle_machine_correct δ start C spec).trans Arithmetic.counter_iff

end CollatzTM
