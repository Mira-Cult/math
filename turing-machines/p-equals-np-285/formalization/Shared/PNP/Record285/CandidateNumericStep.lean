import Shared.PNP.Record285.RelativeTape

/-! An absorbing two-half-tape presentation of the selected deterministic
candidate. It retains the whole numeric tape halves and exact HALT time. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.CandidateNumericStep
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.RelativeTape

/-- Numeric presentation with the currently scanned cell at the low bit of
`right`. State zero is absorbing after a HALT transition. -/
structure Config where
  left : Nat
  right : Nat
  state : Nat
  deriving DecidableEq, Repr

def toSim (c : Config) : SimState :=
  ⟨c.left,c.right/2,c.state-1+2*(c.right%2),0⟩

def step (program : Nat) (c : Config) : Config :=
  if c.state = 0 then c else
    let a := rowAction program c.state (c.right.testBit 0) false
    if a.turn then ⟨2*(c.right/2)+bitVal a.write,c.left,a.next⟩
    else ⟨2*c.left+bitVal a.write,c.right/2,a.next⟩

def run (program : Nat) (c : Config) : Nat → Config
  | 0 => c
  | n+1 => step program (run program c n)

@[simp] theorem run_zero (program : Nat) (c : Config) : run program c 0 = c := rfl
@[simp] theorem run_succ (program : Nat) (c : Config) (n : Nat) :
    run program c (n+1) = step program (run program c n) := rfl

theorem run_zero_state (program : Nat) (c : Config) (hc : c.state = 0) (n : Nat) :
    run program c n = c := by
  induction n with
  | zero => rfl
  | succ n ih => simp [run,ih,step,hc]

/-- An exact algebraic form of the source's next-state operation. -/
theorem simStep_as_action (program : Nat) (s : SimState) :
    let a := action program s
    simStep program s = if a.next = 0 then none else
      some ⟨behindNumber s.left s.right a.write a.turn,
        aheadNumber s.left s.right a.turn,
        a.next-1+2*bitVal (nextRead s.left s.right a.turn),s.choices/2⟩ := by
  have h := action_arithmetic program s
  dsimp only at h ⊢
  rcases h with ⟨hl,hr,hb⟩
  unfold simStep
  dsimp only
  rw [←hl,←hr,←hb]
  rfl

/-- In a live state, the source simulator and the two-half presentation take
exactly the same step. On HALT the latter records state zero after the write. -/
theorem step_matches (program : Nat) (c : Config) (hc : c.state ≠ 0) :
    simStep program (toSim c) =
      if (step program c).state = 0 then none else some (toSim (step program c)) := by
  have hs : (toSim c).selector = c.state-1+2*bitVal (c.right.testBit 0) := by
    simp only [toSim]
    rw [bitVal_lowBit]
  have ha := action_matches_row program c.state (toSim c) (c.right.testBit 0) hs
  have hz : (toSim c).choices.testBit 0 = false := by simp [toSim]
  rw [hz] at ha
  rw [simStep_as_action,ha]
  unfold step
  rw [if_neg hc]
  generalize he : rowAction program c.state (c.right.testBit 0) false = a
  have hb (x : Nat) : (if x%2=1 then 1 else 0) = x%2 := by
    simpa [bitVal] using bitVal_decide_one (x%2) (Nat.mod_lt _ (by decide))
  cases a with
  | mk write turn next =>
    cases turn <;> cases write <;>
      simp [toSim,behindNumber,aheadNumber,nextRead,bitVal,Nat.testBit_zero,hb]

theorem run_front (program : Nat) (c : Config) (n : Nat) :
    run program c (n+1) = run program (step program c) n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [run_succ,ih c,run_succ]

/-- A zero state is absorbing, hence checking state zero after exactly `n`
iterations agrees with the source's HALT-within-`n` observation. -/
theorem run_matches (program : Nat) (c : Config) (hc : c.state ≠ 0) (clock : Nat) :
    haltedWithin program clock (toSim c) = true ↔ (run program c clock).state = 0 := by
  induction clock generalizing c with
  | zero => simp [haltedWithin,hc]
  | succ clock ih =>
    have hs := step_matches program c hc
    by_cases hstep : (step program c).state = 0
    · simp [hstep] at hs
      have hr := run_zero_state program (step program c) hstep clock
      rw [run_front,hr]
      simp [haltedWithin,hs,hstep]
    · simp [hstep] at hs
      rw [run_front]
      simpa [haltedWithin,hs] using ih (step program c) hstep

/-- Exact bounded candidate semantics from its actual numeric input. -/
theorem candidate_as_run (program exponent n radix remaining : Nat) :
    candidate program exponent n radix remaining = true ↔
      (run program ⟨0,frame radix remaining,1⟩ ((n+2)^exponent)).state = 0 := by
  have h := run_matches program ⟨0,frame radix remaining,1⟩ (by simp) ((n+2)^exponent)
  simpa [candidate,toSim] using h

end Shared.PNP.Record285.CandidateNumericStep
