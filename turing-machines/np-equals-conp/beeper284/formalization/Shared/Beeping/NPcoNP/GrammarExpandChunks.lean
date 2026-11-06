import Shared.Beeping.NPcoNP.GrammarExpandSteps

/-! Composition of finite traces for the explicit-stack grammar expander.
Certificates for concrete chunks are still required for any particular input. -/
namespace Shared.Beeping.NPcoNP.Grammar284.ExpandSteps

deriving instance DecidableEq for Expansion
deriving instance DecidableEq for Frame
deriving instance DecidableEq for State

/-- Execute the first `n` steps and then the next `m` steps. -/
theorem steps_add (nodes : Array (Leaf × Leaf)) (n m : Nat) (s : State) :
    steps nodes (n + m) s = (steps nodes n s).bind (steps nodes m) := by
  induction n generalizing s with
  | zero => simp [steps]
  | succ n ih =>
    simp only [Nat.succ_add, steps]
    cases hs : step nodes s with
    | none => simp
    | some t => simp [ih]

/-- Separately established successful chunks compose to a successful trace. -/
theorem chunks (nodes : Array (Leaf × Leaf)) (n m : Nat) (s t u : State)
    (h : steps nodes n s = some t) (h' : steps nodes m t = some u) :
    steps nodes (n + m) s = some u := by
  rw [steps_add, h]
  exact h'

/-- A tiny exact-state control; it does not check the producer grammar. -/
example :
    steps #[(.op "beep", .op "foo")] 3
      ⟨[⟨3, .node 0, [true, true, false], []⟩], {}⟩ =
    some ⟨[], ⟨#[([true, true, false], 0),
                 ([true, true, false, false], 0),
                 ([true, true, false, true], 1)],
                #[([true, true, false, false], "beep"),
                  ([true, true, false, true], "foo")]⟩⟩ := by decide

end Shared.Beeping.NPcoNP.Grammar284.ExpandSteps
