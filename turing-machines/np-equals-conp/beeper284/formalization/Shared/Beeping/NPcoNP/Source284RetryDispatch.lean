import Shared.Beeping.NPcoNP.Source284MatchGrow

/-! Route the comparator's payload-longer outcome into the reset-and-grow
operation. The other two entries execute caller-provided continuations 1 and
2; the grow path enters caller continuation 0 after its paid work. -/
namespace Shared.Beeping.NPcoNP.Source284RetryDispatch

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig shiftRow run_front)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then shiftRow 49 (continuation 1 b)
  else if q = 1 then shiftRow 3 (Source284MatchGrow.table continuation 0 b)
  else if q = 2 then shiftRow 49 (continuation 2 b)
  else shiftRow 3 (Source284MatchGrow.table continuation (q-3) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 3 ≤ states) (hv : Closed states continuation) : Closed (49+states) (table continuation) := by
  have hg := Source284MatchGrow.closed states continuation (by omega) hv
  intro q hq b q' hnext
  by_cases h0 : q = 0
  · subst q
    have ht : (shiftRow 49 (continuation 1 b)).next = some q' := by simpa [table] using hnext
    cases he : (continuation 1 b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hv 1 (by omega) b r he
      simp [shiftRow,he] at ht
      subst q'
      omega
  · by_cases h1 : q = 1
    · subst q
      have ht : (shiftRow 3 (Source284MatchGrow.table continuation 0 b)).next = some q' := by
        simpa [table] using hnext
      cases he : (Source284MatchGrow.table continuation 0 b).next with
      | none => simp [shiftRow,he] at ht
      | some r =>
        have h := hg 0 (by omega) b r he
        simp [shiftRow,he] at ht
        subst q'
        omega
    · by_cases h2 : q = 2
      · subst q
        have ht : (shiftRow 49 (continuation 2 b)).next = some q' := by simpa [table] using hnext
        cases he : (continuation 2 b).next with
        | none => simp [shiftRow,he] at ht
        | some r =>
          have h := hv 2 (by omega) b r he
          simp [shiftRow,he] at ht
          subst q'
          omega
      · have ht : (shiftRow 3 (Source284MatchGrow.table continuation (q-3) b)).next = some q' := by
          simpa [table,h0,h1,h2] using hnext
        have hq0 : q-3 < 46+states := by omega
        cases he : (Source284MatchGrow.table continuation (q-3) b).next with
        | none => simp [shiftRow,he] at ht
        | some r =>
          have h := hg (q-3) hq0 b r he
          simp [shiftRow,he] at ht
          subst q'
          omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (3+q) b = shiftRow 3 (Source284MatchGrow.table continuation q b) := by
  have h0 : 3+q ≠ 0 := by omega
  have h1 : 3+q ≠ 1 := by omega
  have h2 : 3+q ≠ 2 := by omega
  simp [table,h0,h1,h2]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 3 c) =
      shiftConfig 3 (step (Source284MatchGrow.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 3 c) fuel =
      shiftConfig 3 (run (Source284MatchGrow.table continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem enter (continuation : Nat → Bool → Row) (left right : Nat) :
    step (table continuation) ⟨left,right,some 1⟩ =
      shiftConfig 3 (step (Source284MatchGrow.table continuation) ⟨left,right,some 0⟩) := by
  simp [step,table,shiftConfig,shiftRow]
  split <;> rfl

/-- The entry transition is the first reset-and-grow transition, not an
uncharged jump or stutter. -/
theorem run_retry (continuation : Nat → Bool → Row) (left right fuel : Nat) (hpos : 0 < fuel) :
    run (table continuation) ⟨left,right,some 1⟩ fuel =
      shiftConfig 3 (run (Source284MatchGrow.table continuation) ⟨left,right,some 0⟩ fuel) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
  rw [run_front,run_front,enter,relocated_run]

end Shared.Beeping.NPcoNP.Source284RetryDispatch
