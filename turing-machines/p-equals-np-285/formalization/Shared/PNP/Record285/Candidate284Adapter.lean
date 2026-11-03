import Shared.PNP.Record285.CandidateNumericStep
import Shared.PNP.Record285.FiniteRelative
import Shared.Beeping.NPcoNP.Source284TableRun
import Shared.Beeping.NPcoNP.Source284EvaluatorAccept

/-! Recode each fixed 285-source deterministic candidate into the existing
284 unary-clock evaluator. The 284 evaluator is an auxiliary canonical TM2
algorithm, not the 285 record machine. All tape halves and exact clocks are
preserved. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.Candidate284Adapter
open Shared.PNP.Record285.RelativeTape
open Shared.PNP.Record285.FiniteRelative
open Shared.PNP.Record285.CandidateNumericStep
open Shared.Beeping.NPcoNP

/-- A fixed 285 source row with the source's deterministic zero choice. -/
def table (program : Nat) (q : Nat) (read : Bool) : Source284TableEncode.Row :=
  let a := rowAction program q read false
  ⟨a.write,a.turn,if a.next = 0 then none else some a.next⟩

def encode (program bits : Nat) : Nat := Source284TableEncode.encode (stateCap bits) (table program) 0

def toCandidate (c : Source284TableRun.Config) : CandidateNumericStep.Config :=
  ⟨c.left,c.right,c.state.getD 0⟩

def Good (c : Source284TableRun.Config) : Prop :=
  ∀ q, c.state = some q → q ≠ 0

/-- A continuing source transition always has a positive target. -/
theorem table_next_positive (program q : Nat) (read : Bool) (target : Nat)
    (h : (table program q read).next = some target) : target ≠ 0 := by
  simp only [table] at h
  split at h
  · contradiction
  · rename_i hn
    cases h
    exact hn

theorem good_step (program : Nat) (c : Source284TableRun.Config) :
    Good (Source284TableRun.step (table program) c) := by
  rcases c with ⟨l,r,s⟩
  cases s with
  | none => simp [Good,Source284TableRun.step]
  | some q =>
    simp only [Source284TableRun.step]
    split_ifs <;> simp only [Good]
    all_goals intro target ht
    all_goals exact table_next_positive program q (r.testBit 0) target ht

theorem good_run (program : Nat) (c : Source284TableRun.Config) (h : Good c) (clock : Nat) :
    Good (Source284TableRun.run (table program) c clock) := by
  induction clock with
  | zero => exact h
  | succ n ih => exact good_step program _

/-- This comparison includes the actual write and move on the HALT row. -/
theorem step_matches (program : Nat) (c : Source284TableRun.Config) (h : Good c) :
    CandidateNumericStep.step program (toCandidate c) =
      toCandidate (Source284TableRun.step (table program) c) := by
  rcases c with ⟨l,r,s⟩
  cases s with
  | none => rfl
  | some q =>
    have hq : q ≠ 0 := h q rfl
    simp only [toCandidate,Option.getD_some,CandidateNumericStep.step,hq, ↓reduceIte,
      Source284TableRun.step,table]
    by_cases ht : (rowAction program q (r.testBit 0) false).turn = true <;>
      by_cases hn : (rowAction program q (r.testBit 0) false).next = 0 <;>
        simp only [Nat.testBit_zero] at ht hn <;>
        simp [ht,hn,toCandidate,Source284TableEncode.bit,bitVal]

/-- All finite steps, including post-HALT iterations, preserve both numeric
halves and the state. -/
theorem run_matches (program : Nat) (c : Source284TableRun.Config) (h : Good c) (clock : Nat) :
    CandidateNumericStep.run program (toCandidate c) clock =
      toCandidate (Source284TableRun.run (table program) c clock) := by
  induction clock with
  | zero => rfl
  | succ n ih =>
    simp only [CandidateNumericStep.run_succ,Source284TableRun.run]
    rw [ih,step_matches program _ (good_run program c h n)]

/-- The source program's finite bit size bounds all recoded live targets. -/
theorem table_closed (program bits : Nat) (hprogram : program < 2^bits) :
    Source284TableRun.Closed (stateCap bits) (table program) := by
  intro q hq read target ht
  have hb := rowAction_next_le_bits program q bits read false hprogram
  simp only [table] at ht
  split at ht
  · contradiction
  · cases ht
    unfold stateCap
    omega

theorem initial_good (input : Nat) : Good ⟨0,input,some 1⟩ := by
  intro q hq
  simp at hq
  omega

theorem initial_valid (bits input : Nat) : Source284TableRun.Valid (stateCap bits) ⟨0,input,some 1⟩ := by
  intro q hq
  simp at hq
  subst q
  unfold stateCap
  omega

/-- The reused source evaluator accepts at exactly the 285 candidate's clock,
with the initial state explicitly renumbered and both blank/input tapes exact. -/
theorem candidate_iff_source284 (program bits : Nat) (hprogram : program < 2^bits)
    (exponent size radix remaining : Nat) :
    Shared.PNP.Record285.Source.candidate program exponent size radix remaining = true ↔
      (Source284Relative.run (encode program bits)
        ⟨0,Shared.PNP.Record285.Source.frame radix remaining,Source284TableEncode.active 1⟩
        ((size+2)^exponent)).state = 0 := by
  let input := Shared.PNP.Record285.Source.frame radix remaining
  let c : Source284TableRun.Config := ⟨0,input,some 1⟩
  let clock := (size+2)^exponent
  have hrun := Source284TableRun.run_toSource (stateCap bits) (table program) 0 c
    (table_closed program bits hprogram) (initial_valid bits input) clock
  have hmatch := run_matches program c (initial_good input) clock
  have hg := good_run program c (initial_good input) clock
  have he : (toCandidate (Source284TableRun.run (table program) c clock)).state = 0 ↔
      (Source284TableRun.toSource (Source284TableRun.run (table program) c clock)).state = 0 := by
    generalize Source284TableRun.run (table program) c clock = d at hg ⊢
    rcases d with ⟨l,r,s⟩
    cases s with
    | none => rfl
    | some q =>
      have hq := hg q rfl
      simp [toCandidate,Source284TableRun.toSource,Source284TableEncode.nextState,
        Source284TableEncode.active,hq]
  have hc := CandidateNumericStep.candidate_as_run program exponent size radix remaining
  change Shared.PNP.Record285.Source.candidate program exponent size radix remaining = true ↔ _
  rw [hc]
  change (CandidateNumericStep.run program (toCandidate c) clock).state = 0 ↔ _
  rw [hmatch,he,←hrun]
  rfl

end Shared.PNP.Record285.Candidate284Adapter
