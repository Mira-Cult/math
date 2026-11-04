import Shared.PNP.Record285.Source

/-! Executable natural-number model of the two nested unary-decoder loops in
`selected_source.py`. This is a manually transcribed local model, not a checked
translation of the Python AST. Natural subtraction at zero is saturated;
unreachable negative Python integers are outside this model. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonDecoder
open Shared.PNP.Record285.Source

/-- The Python inner loop counts a low-order run of ones, then consumes the
zero delimiter (which may be virtual when the finite number is exhausted). -/
def pop (digit count : Nat) : Nat × Nat :=
  if digit % 2 = 1 then pop (digit / 2) (count + 1)
  else (count,digit / 2)
termination_by digit
decreasing_by omega

theorem pop_correct (digit count : Nat) :
    pop digit count = (count + (popUnary digit).1,(popUnary digit).2) := by
  induction digit using Nat.strongRecOn generalizing count with
  | ind digit ih =>
    by_cases h : digit % 2 = 1
    · have hp : 0 < digit := by omega
      rw [pop, popUnary]
      simp only [h, ↓reduceIte, ↓reduceDIte]
      rw [ih (digit/2) (by omega)]
      congr 1 <;> omega
    · rw [pop, popUnary]
      simp [h]

/-- `place` counts the Python outer loop. Its last iteration's unary count
is the packed action; the initial state is overwritten on every iteration. -/
def select : Nat → Nat → Nat → Nat × Nat
  | 0, digit, state => (state,digit)
  | place+1, digit, _ =>
      let decoded := pop digit 0
      select place decoded.2 decoded.1

theorem select_succ_correct (place digit state : Nat) :
    select (place+1) digit state = popUnary (skipUnary place digit) := by
  induction place generalizing digit state with
  | zero => simp [select,skipUnary,pop_correct]
  | succ place ih =>
    rw [select, pop_correct]
    simp only [Nat.zero_add]
    rw [ih]
    rfl

/-- Explicit Python-style configuration: the symbol under the head is kept
separately from the right-hand numeric tape, and `state` is one-based. -/
structure State where
  left : Nat
  right : Nat
  state : Nat
  read : Nat
  choices : Nat
  deriving DecidableEq, Repr

def abstract (s : State) : SimState :=
  ⟨s.left,s.right,s.state - 1 + 2*s.read,s.choices⟩

/-- One Python `accept` loop iteration, after decoding the unary action into
its write, direction and next-state components. -/
def step (program : Nat) (s : State) : Option State :=
  let place := s.state + 2*s.read + s.choices%2
  let packed := (select place program s.state).1
  let write := packed%2
  let direction := (packed/2)%2
  let next := packed/4
  let left := if direction = 0 then s.left else s.right
  let right := if direction = 0 then s.right else s.left
  if next = 0 then none
  else some ⟨2*left+write,right/2,next,right%2,s.choices/2⟩

/-- The actual Python loop always tests for zero before using a new state.
Under this positive-state invariant, the explicit one-based configuration
and the source's packed selector have exactly the same transition. -/
theorem step_correct (program : Nat) (s : State) (hs : 0 < s.state) :
    Option.map abstract (step program s) = simStep program (abstract s) := by
  have hplace : s.state + 2*s.read + s.choices%2 =
      (s.state-1+2*s.read+s.choices%2)+1 := by omega
  simp only [step,abstract,simStep]
  rw [hplace,select_succ_correct]
  by_cases hz : (popUnary (skipUnary (s.state-1+2*s.read+s.choices%2) program)).1/4=0
  · simp [hz]
  · simp [hz,abstract]
    exact ⟨rfl,rfl,rfl⟩

theorem step_positive (program : Nat) (s next : State)
    (h : step program s = some next) : 0 < next.state := by
  unfold step at h
  dsimp only at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    subst next
    simp_all

/-- Bounded Python evaluator; `none` is returned as soon as the decoded
transition enters state zero. -/
def run (program : Nat) : Nat → State → Option State
  | 0, s => some s
  | clock+1, s =>
      match step program s with
      | none => none
      | some next => run program clock next

theorem run_correct (program clock : Nat) (s : State) (hs : 0 < s.state) :
    Option.map abstract (run program clock s) = runSteps program clock (abstract s) := by
  induction clock generalizing s with
  | zero => rfl
  | succ clock ih =>
    have hstep := step_correct program s hs
    cases h : step program s with
    | none =>
      have hsrc : simStep program (abstract s) = none := by simpa [h] using hstep.symm
      simp [run,runSteps,h,hsrc]
    | some next =>
      have hsrc : simStep program (abstract s) = some (abstract next) := by simpa [h] using hstep.symm
      have hn := step_positive program s next h
      simpa [run,runSteps,h,hsrc] using ih next hn

def initial (input branch : Nat) : State :=
  ⟨0,input/2,1,input%2,branch⟩

/-- Direct bounded model of the standalone Python `accept` branch search. -/
def accept (program input clock : Nat) : Nat → Bool
  | 0 => false
  | branches+1 =>
      if (run program clock (initial input branches)).isNone then true
      else accept program input clock branches

theorem halted_correct (program input clock branch : Nat) :
    (run program clock (initial input branch)).isNone =
      haltedWithin program clock ⟨0,input/2,2*(input%2),branch⟩ := by
  have hr := run_correct program clock (initial input branch) (by simp [initial])
  have hs : abstract (initial input branch) = ⟨0,input/2,2*(input%2),branch⟩ := by
    simp [abstract,initial]
  rw [hs] at hr
  apply Bool.eq_iff_iff.mpr
  rw [Option.isNone_iff_eq_none,haltedWithin_iff_runSteps]
  rw [← hr]
  cases run program clock (initial input branch) <;> simp

/-- On zero input, the Python branch loop is exactly the Lean reference
search, for every program, clock and branch bound. -/
theorem accept_zero_correct (program clock branches : Nat) :
    accept program 0 clock branches = referenceSearch program clock branches := by
  induction branches with
  | zero => rfl
  | succ branches ih =>
    simp [accept,referenceSearch,halted_correct,ih]

/-- One branch of the standalone evaluator on the source frame agrees with
the source's deterministic candidate for all natural inputs and clocks. -/
theorem accept_candidate_correct (program exponent n radix remaining : Nat) :
    accept program (frame radix remaining) ((n+2)^exponent) 1 =
      candidate program exponent n radix remaining := by
  simp [accept,candidate,halted_correct]

/-- The two bounded searches implement the comparison performed by the
source controller, for every natural input, including zero clocks and radix. -/
theorem comparison_correct (program exponent n radix remaining : Nat) :
    (accept (radix+remaining) 0 n radix !=
      accept program (frame radix remaining) ((n+2)^exponent) 1) =
        mismatch program exponent n radix remaining := by
  rw [accept_zero_correct,accept_candidate_correct]
  rfl

end Shared.PNP.Record285.PythonDecoder
