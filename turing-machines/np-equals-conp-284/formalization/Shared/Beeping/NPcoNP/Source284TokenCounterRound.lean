import Shared.Beeping.NPcoNP.Source284ScratchCounterExtend
import Shared.Beeping.NPcoNP.Source284UnaryMarkOne

/-! One finite source-table round: mark one unary token and extend a suffix
counter, or select a distinct exhaustion continuation. The two branches have
explicit positive runtimes. Repeating successful rounds autonomously is a
separate control-flow obligation. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284TokenCounterRound

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

/-- Two turns restore the head; mode zero selects counter extension and
mode one selects the separate exhaustion continuation. -/
def dispatch (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,true,some 2⟩
  else if q = 1 then ⟨b,true,some 3⟩
  else if q = 2 then ⟨b,true,some 4⟩
  else if q = 3 then ⟨b,true,some 21⟩
  else shiftRow 4 (Source284ScratchCounterExtend.table continuation (q-4) b)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284UnaryMarkOne.table (dispatch continuation)

theorem dispatch_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 2 ≤ states) (hv : Closed states continuation) : Closed (20+states) (dispatch continuation) := by
  have hc := Source284ScratchCounterExtend.closed states continuation (by omega) hv
  intro q hq b q' hnext
  by_cases hsmall : q < 4
  · interval_cases q <;> cases b <;> simp [dispatch] at hnext <;> omega
  · have he : (shiftRow 4 (Source284ScratchCounterExtend.table continuation (q-4) b)).next = some q' := by
      simpa [dispatch,show q ≠ 0 by omega,show q ≠ 1 by omega,
        show q ≠ 2 by omega,show q ≠ 3 by omega] using hnext
    cases hh : (Source284ScratchCounterExtend.table continuation (q-4) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hc (q-4) (by omega) b r hh
      simp [shiftRow,hh] at he
      subst q'; omega

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 2 ≤ states) (hv : Closed states continuation) : Closed (32+states) (table continuation) := by
  have h := Source284UnaryMarkOne.closed (20+states) (dispatch continuation) (by omega)
    (dispatch_closed states continuation hn hv)
  have he : 12+(20+states) = 32+states := by omega
  rw [he] at h
  exact h

theorem dispatch_relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    dispatch continuation (4+q) b = shiftRow 4 (Source284ScratchCounterExtend.table continuation q b) := by
  simp [dispatch,show 4+q ≠ 1 by omega,show 4+q ≠ 2 by omega,show 4+q ≠ 3 by omega]

theorem dispatch_relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (dispatch continuation) (shiftConfig 4 c) =
      shiftConfig 4 (step (Source284ScratchCounterExtend.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,dispatch_relocated_row,shiftRow]
      split <;> rfl

theorem dispatch_relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (dispatch continuation) (shiftConfig 4 c) fuel =
      shiftConfig 4 (run (Source284ScratchCounterExtend.table continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,dispatch_relocated_step]

theorem dispatch_two (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 2)
    (left right : Nat) :
    run (dispatch continuation) ⟨left,right,some mode⟩ 2 =
      ⟨left,right,some (if mode = 0 then 4 else 21)⟩ := by
  interval_cases mode <;>
    simp [run,step,dispatch,bit,Nat.testBit_zero] <;> split_ifs <;> omega

theorem dispatch_found (continuation : Nat → Bool → Row) (w : List Bool)
    (n certificate higher : Nat) :
    run (dispatch continuation) ⟨certificate,2*flipped w (counter n higher),some 0⟩
      (2+(4*w.length+2*n+16)) =
      ⟨certificate,2*flipped w (counter (n+1) (higher/2)),some 20⟩ := by
  rw [Source284ScratchScanner.run_add,dispatch_two _ 0 (by decide)]
  change run (dispatch continuation) (shiftConfig 4
    ⟨certificate,2*flipped w (counter n higher),some 0⟩) _ = _
  rw [dispatch_relocated_run,Source284ScratchCounterExtend.extend_scratch]
  rfl

/-- One available unary token is marked and the counter is extended once.
The payload, marker count, certificate and high suffix are tracked exactly. -/
theorem token_found (continuation : Nat → Bool → Row) (k : Nat) (rest : List Bool)
    (w : List Bool) (n certificate higher : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate k true ++ false::rest) certificate,
        2*flipped w (counter n higher),some 0⟩ (4*k+4*w.length+2*n+24) =
      ⟨pairTape (List.replicate k true ++ true::rest) certificate,
        2*flipped w (counter (n+1) (higher/2)),some 32⟩ := by
  have ht : 4*k+4*w.length+2*n+24 = (4*k+6)+(2+(4*w.length+2*n+16)) := by omega
  rw [ht,Source284ScratchScanner.run_add]
  change run (Source284UnaryMarkOne.table (dispatch continuation))
    (run (Source284UnaryMarkOne.table (dispatch continuation)) _ _) _ = _
  rw [Source284UnaryMarkOne.mark_first]
  change run (Source284UnaryMarkOne.table (dispatch continuation))
    (shiftConfig 12 ⟨pairTape (List.replicate k true ++ true::rest) certificate,
      2*flipped w (counter n higher),some 0⟩) _ = _
  rw [Source284UnaryMarkOne.relocated_run,dispatch_found]
  rfl

/-- Exhaustion leaves both halves unchanged and selects a different
continuation state, including the zero-token case. -/
theorem token_exhausted (continuation : Nat → Bool → Row) (k : Nat)
    (w : List Bool) (n certificate higher : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate k true) certificate,2*flipped w (counter n higher),some 0⟩
      (4*k+8) =
      ⟨pairTape (List.replicate k true) certificate,2*flipped w (counter n higher),some 33⟩ := by
  have ht : 4*k+8 = (4*k+6)+2 := by omega
  rw [ht,Source284ScratchScanner.run_add]
  change run (Source284UnaryMarkOne.table (dispatch continuation))
    (run (Source284UnaryMarkOne.table (dispatch continuation)) _ _) _ = _
  rw [Source284UnaryMarkOne.all_marked]
  change run (Source284UnaryMarkOne.table (dispatch continuation))
    (shiftConfig 12 ⟨pairTape (List.replicate k true) certificate,
      2*flipped w (counter n higher),some 1⟩) 2 = _
  rw [Source284UnaryMarkOne.relocated_run,dispatch_two _ 1 (by decide)]
  rfl

end Shared.Beeping.NPcoNP.Source284TokenCounterRound
