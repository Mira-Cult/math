import Shared.Beeping.NPcoNP.Source284MatchLoopComplete
import Shared.Beeping.NPcoNP.Source284MatchReset
import Shared.Beeping.NPcoNP.Source284ScratchShiftCycle

/-! One source-table comparison round: restore both tapes and add a token
when the input is longer, or restore them and report equality. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284LengthGrowRound

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig shiftRow)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def sink (q : Nat) (b : Bool) : Row := ⟨b,false,some q⟩

def grow : Nat → Bool → Row :=
  Source284MatchReset.table (Source284ScratchShiftCycle.repeatTable 2 sink)

def equal : Nat → Bool → Row := Source284MatchReset.table sink

/-- Entries one and two pay two turns before their respective reset paths.
Entry zero is the unused extra-token branch. -/
def dispatch (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,false,some 0⟩
  else if q = 1 then ⟨b,true,some 3⟩
  else if q = 2 then ⟨b,true,some 4⟩
  else if q = 3 then ⟨b,true,some 5⟩
  else if q = 4 then ⟨b,true,some 52⟩
  else if q < 52 then shiftRow 5 (grow (q-5) b)
  else shiftRow 52 (equal (q-52) b)

def table : Nat → Bool → Row := Source284MatchLoop.table dispatch

theorem sink_closed : Closed 1 sink := by
  intro q hq b q' h
  simp [sink] at h
  omega

theorem grow_closed : Closed 47 grow := by
  have h := Source284ScratchShiftCycle.repeat_closed 2 1 sink (by decide) sink_closed
  have h' := Source284MatchReset.closed 29 (Source284ScratchShiftCycle.repeatTable 2 sink) (by decide) (by simpa using h)
  simpa [grow] using h'

theorem equal_closed : Closed 19 equal := by
  have h := Source284MatchReset.closed 1 sink (by decide) sink_closed
  simpa [equal] using h

theorem dispatch_closed : Closed 71 dispatch := by
  intro q hq b q' hnext
  by_cases hs : q < 5
  · interval_cases q <;> simp [dispatch] at hnext <;> omega
  · by_cases hg : q < 52
    · have he : (shiftRow 5 (grow (q-5) b)).next = some q' := by
        simpa [dispatch,show q ≠ 0 by omega,show q ≠ 1 by omega,
          show q ≠ 2 by omega,show q ≠ 3 by omega,show q ≠ 4 by omega,hg] using hnext
      cases hh : (grow (q-5) b).next with
      | none => simp [shiftRow,hh] at he
      | some r =>
        have hr := grow_closed (q-5) (by omega) b r hh
        simp [shiftRow,hh] at he
        subst q'; omega
    · have he : (shiftRow 52 (equal (q-52) b)).next = some q' := by
        simpa [dispatch,show q ≠ 0 by omega,show q ≠ 1 by omega,
          show q ≠ 2 by omega,show q ≠ 3 by omega,show q ≠ 4 by omega,hg] using hnext
      cases hh : (equal (q-52) b).next with
      | none => simp [shiftRow,hh] at he
      | some r =>
        have hr := equal_closed (q-52) (by omega) b r hh
        simp [shiftRow,hh] at he
        subst q'; omega

theorem closed : Closed 119 table := by
  have h := Source284MatchLoop.closed 71 dispatch (by decide) dispatch_closed
  simpa [table] using h

theorem enter (mode left right : Nat) (hm : mode = 1 ∨ mode = 2) :
    run dispatch ⟨left,right,some mode⟩ 2 =
      ⟨left,right,some (if mode = 1 then 5 else 52)⟩ := by
  rcases hm with rfl | rfl <;>
    simp [run,step,dispatch,bit,Nat.testBit_zero] <;> split_ifs <;> omega

theorem grow_row (q : Nat) (hq : q < 47) (b : Bool) :
    dispatch (5+q) b = shiftRow 5 (grow q b) := by
  simp [dispatch,show 5+q ≠ 1 by omega,show 5+q ≠ 2 by omega,
    show 5+q ≠ 3 by omega,show 5+q ≠ 4 by omega,show 5+q < 52 by omega]

theorem grow_step (c : Config) (hc : Valid 47 c) :
    step dispatch (shiftConfig 5 c) = shiftConfig 5 (step grow c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      have hq := hc q rfl
      simp only [shiftConfig,Option.map_some,step,grow_row q hq,shiftRow]
      split <;> rfl

theorem grow_run (c : Config) (hc : Valid 47 c) (fuel : Nat) :
    run dispatch (shiftConfig 5 c) fuel = shiftConfig 5 (run grow c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    simp only [run,ih]
    exact grow_step _ (valid_run 47 grow c grow_closed hc fuel)

theorem equal_row (q : Nat) (b : Bool) :
    dispatch (52+q) b = shiftRow 52 (equal q b) := by
  simp [dispatch,show 52+q ≠ 1 by omega,show 52+q ≠ 2 by omega,
    show 52+q ≠ 3 by omega,show 52+q ≠ 4 by omega,show ¬ 52+q < 52 by omega]

theorem equal_step (c : Config) :
    step dispatch (shiftConfig 52 c) = shiftConfig 52 (step equal c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,equal_row,shiftRow]
      split <;> rfl

theorem equal_run (c : Config) (fuel : Nat) :
    run dispatch (shiftConfig 52 c) fuel = shiftConfig 52 (run equal c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,equal_step]

/-- Reset both marked regions, then perform two actual scratch shifts. -/
theorem grow_processed (tokens xs rest : List Bool) (certificate tail : Nat) :
    run grow ⟨pairTape tokens certificate,2*zeros xs (flipped (rest++[false]) tail),some 0⟩
      ((4*tokens.length+6)+(4*(xs.length+rest.length)+12) +
        2*(4*((xs++rest)++[false]).length+7)) =
    ⟨4*pairTape (List.replicate tokens.length false) certificate,
      2*flipped ((xs++rest)++[false]) (tail/4),some 46⟩ := by
  unfold grow
  rw [run_add,Source284MatchReset.reset]
  change run (Source284MatchReset.table (Source284ScratchShiftCycle.repeatTable 2 sink))
    (shiftConfig 7 (shiftConfig 5 (shiftConfig 6
      ⟨pairTape (List.replicate tokens.length false) certificate,
        2*flipped ((xs++rest)++[false]) tail,some 0⟩))) _ = _
  unfold Source284MatchReset.table
  rw [Source284UnaryClear.relocated_run,Source284PayloadReset.relocated_run,
    Source284ScratchFlipReturn.relocated_run,Source284ScratchShiftCycle.repeat_run]
  rfl

theorem equal_processed (tokens xs rest : List Bool) (certificate tail : Nat) :
    run equal ⟨pairTape tokens certificate,2*zeros xs (flipped (rest++[false]) tail),some 0⟩
      ((4*tokens.length+6)+(4*(xs.length+rest.length)+12)) =
    ⟨pairTape (List.replicate tokens.length false) certificate,
      2*flipped ((xs++rest)++[false]) tail,some 18⟩ := by
  exact Source284MatchReset.reset sink tokens xs rest certificate tail

theorem token_prepend (k certificate : Nat) :
    4*pairTape (List.replicate k false) certificate =
      pairTape (List.replicate (k+1) false) certificate := by
  simp [List.replicate_succ,pairTape,Source284PayloadLoop.scratch,bit]

def compareTime (k : Nat) : Nat := 4*k*k+20*k+16

def growTime (xs rest : List Bool) (b : Bool) : Nat :=
  compareTime xs.length + (2+((4*xs.length+6)+
    (4*((xs++[b]).length+rest.length)+12) +
    2*(4*(((xs++[b])++rest)++[false]).length+7)))

def equalTime (n : Nat) : Nat := compareTime n + (2+((4*n+6)+(4*(n+0)+12)))

/-- When payload remains after the current unary tokens, the one fixed table
marks the mismatch, restores both regions, and adds one unmarked token. -/
theorem grow_round (xs rest : List Bool) (b : Bool) (certificate tail : Nat) :
    run table ⟨pairTape (List.replicate xs.length false) certificate,
      2*flipped ((xs++b::rest)++[false]) tail,some 0⟩ (growTime xs rest b) =
    ⟨pairTape (List.replicate (xs.length+1) false) certificate,
      2*flipped ((xs++b::rest)++[false]) (tail/4),some 99⟩ := by
  unfold growTime compareTime table
  rw [run_add,Source284MatchLoopComplete.more_payload]
  change run (Source284MatchLoop.table dispatch)
    (shiftConfig 48 ⟨pairTape (List.replicate xs.length true) certificate,
      2*zeros (xs++[b]) (flipped (rest++[false]) tail),some 1⟩) _ = _
  rw [Source284MatchLoop.relocated_run,run_add,enter 1 _ _ (Or.inl rfl)]
  change shiftConfig 48 (run dispatch
    (shiftConfig 5 ⟨pairTape (List.replicate xs.length true) certificate,
      2*zeros (xs++[b]) (flipped (rest++[false]) tail),some 0⟩) _) = _
  have hv : Valid 47 ⟨pairTape (List.replicate xs.length true) certificate,
      2*zeros (xs++[b]) (flipped (rest++[false]) tail),some 0⟩ := by
    intro q hq; simp at hq; omega
  rw [grow_run _ hv]
  have hg := grow_processed (List.replicate xs.length true) (xs++[b]) rest certificate tail
  simp only [List.length_replicate] at hg
  rw [hg,token_prepend]
  simp [shiftConfig,List.append_assoc]

/-- At equality the same table restores both halves and selects a distinct
terminal branch; no shift or new token is made. -/
theorem equal_round (w : List Bool) (certificate tail : Nat) :
    run table ⟨pairTape (List.replicate w.length false) certificate,
      2*flipped (w++[false]) tail,some 0⟩ (equalTime w.length) =
    ⟨pairTape (List.replicate w.length false) certificate,
      2*flipped (w++[false]) tail,some 118⟩ := by
  unfold equalTime compareTime table
  rw [run_add,Source284MatchLoopComplete.equal_length]
  change run (Source284MatchLoop.table dispatch)
    (shiftConfig 48 ⟨pairTape (List.replicate w.length true) certificate,
      2*zeros w (flipped ([]++[false]) tail),some 2⟩) _ = _
  rw [Source284MatchLoop.relocated_run,run_add,enter 2 _ _ (Or.inr rfl)]
  change shiftConfig 48 (run dispatch
    (shiftConfig 52 ⟨pairTape (List.replicate w.length true) certificate,
      2*zeros w (flipped ([]++[false]) tail),some 0⟩) _) = _
  rw [equal_run]
  have he := equal_processed (List.replicate w.length true) w [] certificate tail
  simp only [List.length_replicate,List.length_nil] at he
  rw [he]
  simp [shiftConfig]

end Shared.Beeping.NPcoNP.Source284LengthGrowRound
