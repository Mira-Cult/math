import Mathlib.Tactic

/-! The bounded certificate-tape evaluator used by the 284-state NP=coNP
source. Provenance: `problems/np-conp-formulations/selector/continuation/
compact/phase_swap/source.py` in Mira-Cult/math-wip commit
`7b90875183aa928fb19a4a9bf333b8ced2194ded`, SHA-256
`4f1f6f317eb196b8d09a67439893622a759c43ef4e02e30adae4e04b0eb39515`.

The natural description has a virtual zero tail, so every natural number is
a meaningful description: there is no invalid-description exception. This
module defines the bounded source computations; it does not assert a class
equality, polynomial cost, or any compiler/tape-machine refinement. -/

namespace Shared.Beeping.NPcoNP.Source284Relative

/-- The value of one unary `1^a 0` record and the unconsumed description.
A missing terminator is supplied by the infinite virtual zero tail. -/
def readRecord (digit : Nat) : Nat × Nat :=
  if digit % 2 = 1 then
    let result := readRecord (digit / 2)
    (result.1 + 1, result.2)
  else (0, digit / 2)
termination_by digit
decreasing_by
  have h : 0 < digit := by omega
  exact Nat.div_lt_self h (by decide)

theorem readRecord_odd (digit : Nat) (h : digit % 2 = 1) :
    readRecord digit = ((readRecord (digit / 2)).1 + 1, (readRecord (digit / 2)).2) := by
  rw [readRecord]
  simp [h]

theorem readRecord_even (digit : Nat) (h : digit % 2 = 0) :
    readRecord digit = (0, digit / 2) := by
  rw [readRecord]
  simp [h]

@[simp] theorem readRecord_zero : readRecord 0 = (0, 0) := by
  simpa using readRecord_even 0 (by decide)

/-- Consume exactly `ordinal` records, including virtual zero records. -/
def dropRecords : Nat → Nat → Nat
  | digit, 0 => digit
  | digit, ordinal + 1 => dropRecords (readRecord digit).2 ordinal

/-- Record number `ordinal`, counting from zero. -/
def record (description ordinal : Nat) : Nat :=
  (readRecord (dropRecords description ordinal)).1

@[simp] theorem dropRecords_zero_description (ordinal : Nat) : dropRecords 0 ordinal = 0 := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => simpa [dropRecords] using ih

@[simp] theorem record_zero_description (ordinal : Nat) : record 0 ordinal = 0 := by
  simp [record]

/-- Two source tape halves in the current direction. `right` begins at the
scanned cell; `left` begins immediately behind it. State zero is accepting. -/
structure Config where
  left : Nat
  right : Nat
  state : Nat
  deriving DecidableEq, Repr

/-- One bounded-simulation iteration. A zero state is absorbing. Otherwise
the record value independently encodes the write bit, relative turn, and
next state. -/
def step (description : Nat) (c : Config) : Config :=
  if c.state = 0 then c else
    let a := record description (c.state - 1 + c.right % 2)
    let write := a % 2
    let turn := (a / 2) % 2
    let next := a / 4
    let forward := c.right / 2
    if turn = 1 then ⟨2 * forward + write, c.left, next⟩
    else ⟨2 * c.left + write, forward, next⟩

@[simp] theorem step_absorbing (description : Nat) (c : Config) (h : c.state = 0) :
    step description c = c := by simp [step, h]

/-- Exactly `clock` source loop iterations, including the inert iterations
after the accepting state has been reached. -/
def run (description : Nat) (c : Config) : Nat → Config
  | 0 => c
  | clock + 1 => step description (run description c clock)

@[simp] theorem run_zero (description : Nat) (c : Config) : run description c 0 = c := rfl
@[simp] theorem run_succ (description : Nat) (c : Config) (clock : Nat) :
    run description c (clock + 1) = step description (run description c clock) := rfl

theorem run_absorbing (description : Nat) (c : Config) (h : c.state = 0) (clock : Nat) :
    run description c clock = c := by
  induction clock with
  | zero => rfl
  | succ clock ih => simp [run, ih, h]

def initial (input certificate : Nat) : Config := ⟨certificate, input, 1⟩

/-- An individual bounded attempt; a nonzero state at the clock boundary is
rejection, including timeout. The certificate is initially on the negative
half tape and the complete input integer is on the positive half. -/
def accepts (description input certificate clock : Nat) : Bool :=
  (run description (initial input certificate) clock).state == 0

theorem accepts_iff (description input certificate clock : Nat) :
    accepts description input certificate clock = true ↔
      (run description (initial input certificate) clock).state = 0 := by
  simp [accepts]

@[simp] theorem accepts_zero_clock (description input certificate : Nat) :
    accepts description input certificate 0 = false := by simp [accepts, initial]

/-- `A_B`: search every natural certificate below the supplied finite
bound. Search order has no bearing on the returned existential Boolean. -/
def acceptBound (description input clock bound : Nat) : Bool :=
  (List.range bound).any (fun certificate => accepts description input certificate clock)

theorem acceptBound_iff (description input clock bound : Nat) :
    acceptBound description input clock bound = true ↔
      ∃ certificate, certificate < bound ∧ accepts description input certificate clock = true := by
  simp [acceptBound, List.any_eq_true]

@[simp] theorem acceptBound_zero_bound (description input clock : Nat) :
    acceptBound description input clock 0 = false := by simp [acceptBound]

@[simp] theorem acceptBound_zero_clock (description input bound : Nat) :
    acceptBound description input 0 bound = false := by
  simp [acceptBound]

/-- Description zero has only virtual zero records and accepts on its first
transition from state one, regardless of input and certificate. -/
theorem accepts_zero_description_one (input certificate : Nat) :
    accepts 0 input certificate 1 = true := by
  simp [accepts, initial, run, step]

end Shared.Beeping.NPcoNP.Source284Relative
