import Shared.Beeping.NPcoNP.Source284TableEncode

/-! Finite-run correctness for the source unary-record table encoding.
The logical table uses the source's relative direction convention. Its
accepting state is absorbing, just as in the bounded source evaluator.
The table may be an arbitrary Lean function: this result does not establish
effective table serialization, polynomial running time, or a final beeper. -/

namespace Shared.Beeping.NPcoNP.Source284TableRun

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284Relative

structure Config where
  left : Nat
  right : Nat
  state : Option Nat
  deriving DecidableEq, Repr

/-- A logical relative-table step. Acceptance performs the write and move
on its incoming transition and is absorbing on later iterations. -/
def step (table : Nat → Bool → Row) (c : Config) : Config :=
  match c.state with
  | none => c
  | some q =>
    let r := table q (c.right.testBit 0)
    if r.turn then ⟨2 * (c.right / 2) + bit r.write, c.left, r.next⟩
    else ⟨2 * c.left + bit r.write, c.right / 2, r.next⟩

def run (table : Nat → Bool → Row) (c : Config) : Nat → Config
  | 0 => c
  | n + 1 => step table (run table c n)

def toSource (c : Config) : Source284Relative.Config :=
  ⟨c.left, c.right, nextState c.state⟩

def Valid (n : Nat) (c : Config) : Prop :=
  ∀ q, c.state = some q → q < n

/-- Every transition of an in-range state stays in range or accepts. -/
def Closed (n : Nat) (table : Nat → Bool → Row) : Prop :=
  ∀ q, q < n → ∀ b q', (table q b).next = some q' → q' < n

theorem valid_step (n : Nat) (table : Nat → Bool → Row) (c : Config)
    (closed : Closed n table) (valid : Valid n c) : Valid n (step table c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => simpa [step] using valid
    | some q =>
      have hq : q < n := valid q rfl
      cases hnext : (table q (right.testBit 0)).next with
      | none =>
        simp only [Nat.testBit_zero] at hnext
        simp only [step]
        split_ifs <;> simp [Valid, hnext]
      | some q' =>
        have hq' := closed q hq (right.testBit 0) q' hnext
        simp only [Nat.testBit_zero] at hnext
        simp only [step]
        split_ifs <;> simp [Valid, hnext, hq']

theorem valid_run (n : Nat) (table : Nat → Bool → Row) (c : Config)
    (closed : Closed n table) (valid : Valid n c) (k : Nat) :
    Valid n (run table c k) := by
  induction k with
  | zero => exact valid
  | succ k ih => exact valid_step n table _ closed ih

/-- Every step of a represented, in-range logical configuration agrees with
the source evaluator. -/
theorem step_toSource (n : Nat) (table : Nat → Bool → Row) (tail : Nat)
    (c : Config) (valid : Valid n c) :
    Source284Relative.step (encode n table tail) (toSource c) =
      toSource (step table c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => simp [toSource, nextState, step, Source284Relative.step]
    | some q =>
      have hq : q < n := valid q rfl
      have hs := step_lookup n table tail q left right hq
      cases ht : (table q (right.testBit 0)).turn <;>
        simpa only [toSource, nextState, step, ht, Bool.false_eq_true,
          Bool.true_eq_false, ↓reduceIte] using hs

/-- With the finite-state closure invariant, the simulation holds for every
finite number of steps, including iterations after acceptance. -/
theorem run_toSource (n : Nat) (table : Nat → Bool → Row) (tail : Nat)
    (c : Config) (closed : Closed n table) (valid : Valid n c) (k : Nat) :
    Source284Relative.run (encode n table tail) (toSource c) k =
      toSource (run table c k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Source284Relative.run_succ, run, ih]
    exact step_toSource n table tail _ (valid_run n table c closed valid k)

@[simp] theorem nextState_zero (s : Option Nat) : (nextState s == 0) = s.isNone := by
  cases s with
  | none => rfl
  | some q => simp [nextState, active]

/-- When state zero is the logical start, source input and certificate are
placed on exactly the same two tape halves, and bounded acceptance agrees. -/
theorem bounded_acceptance (n : Nat) (table : Nat → Bool → Row) (tail : Nat)
    (hn : 0 < n) (closed : Closed n table) (input certificate k : Nat) :
    Source284Relative.accepts (encode n table tail) input certificate k =
      (run table ⟨certificate, input, some 0⟩ k).state.isNone := by
  have hv : Valid n ⟨certificate, input, some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    omega
  have hr := run_toSource n table tail ⟨certificate, input, some 0⟩ closed hv k
  change ((Source284Relative.run (encode n table tail)
    (toSource ⟨certificate, input, some 0⟩) k).state == 0) = _
  rw [hr]
  exact nextState_zero _

end Shared.Beeping.NPcoNP.Source284TableRun
