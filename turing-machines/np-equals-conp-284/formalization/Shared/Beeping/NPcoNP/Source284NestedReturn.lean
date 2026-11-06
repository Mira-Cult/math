import Shared.Beeping.NPcoNP.Source284NestedMarker
import Shared.Beeping.NPcoNP.Source284UnaryClear

/-! Return across an all-zero inner unary block after the outer marker scan,
restoring its sentinel and the original scratch boundary. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284NestedReturn

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig run_front)
open Shared.Beeping.NPcoNP.Source284ScratchScanner (push)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def enterReturn (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then shiftRow 1 (Source284UnaryClear.table continuation 4 b)
  else shiftRow 1 (Source284UnaryClear.table continuation (q-1) b)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨true,false,some 1⟩
  else if q = 1 then ⟨false,false,some 2⟩
  else shiftRow 2 (enterReturn continuation (q-2) b)

theorem return_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    enterReturn continuation (1+q) b = shiftRow 1 (Source284UnaryClear.table continuation q b) := by
  simp [enterReturn]

theorem return_step (continuation : Nat → Bool → Row) (c : Config) :
    step (enterReturn continuation) (shiftConfig 1 c) =
      shiftConfig 1 (step (Source284UnaryClear.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,return_row,shiftRow]
      split <;> rfl

theorem return_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (enterReturn continuation) (shiftConfig 1 c) fuel =
      shiftConfig 1 (run (Source284UnaryClear.table continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,return_step]

theorem return_jump (continuation : Nat → Bool → Row) (left right fuel : Nat) :
    run (enterReturn continuation) ⟨left,right,some 0⟩ (fuel+1) =
      shiftConfig 1 (run (Source284UnaryClear.table continuation)
        ⟨left,right,some 4⟩ (fuel+1)) := by
  rw [run_front,run_front]
  have hs : step (enterReturn continuation) ⟨left,right,some 0⟩ =
      shiftConfig 1 (step (Source284UnaryClear.table continuation) ⟨left,right,some 4⟩) := by
    simp [step,enterReturn,shiftRow,shiftConfig]
    split <;> rfl
  rw [hs,return_run]

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (2+q) b = shiftRow 2 (enterReturn continuation q b) := by
  simp [table,show 2+q ≠ 1 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 2 c) = shiftConfig 2 (step (enterReturn continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 2 c) fuel = shiftConfig 2 (run (enterReturn continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

/-- Restore the inner all-zero token block and the original tape boundary. -/
theorem restore (continuation : Nat → Bool → Row) (m outer stream : Nat) :
    run (table continuation) ⟨outer,4*push (2*stream+1) (List.replicate m false),some 0⟩ (2*m+4) =
      ⟨pairTape (List.replicate m false) outer,2*stream,some 10⟩ := by
  have ht : 2*m+4 = 2+(2*m+2) := by omega
  rw [ht,Source284ScratchScanner.run_add]
  have hp : run (table continuation)
      ⟨outer,4*push (2*stream+1) (List.replicate m false),some 0⟩ 2 =
      shiftConfig 2 ⟨4*outer+2,push (2*stream+1) (List.replicate m false),some 0⟩ := by
    simp [run,step,table,shiftConfig,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega
  rw [hp,relocated_run]
  have he : 2*m+2 = (2*m+1)+1 := by omega
  rw [he,return_jump,← he]
  have hpw := Source284UnaryPairScanner.push_zeros m (2*stream+1)
  rw [hpw,Source284ScratchScanner.run_add,Source284UnaryClear.back_pairs,
    Source284UnaryClear.restore_boundary]
  have hz : 4^m*(4*outer+2) = pairTape (List.replicate m false) outer := by
    rw [show 4^m = 2^(2*m) by rw [Nat.pow_mul],
      ← Source284ScratchSentinel.unaryPairs_stack,← Source284UnaryPairScanner.zero_pairTape]
  simp only [shiftConfig,Option.map_some]
  rw [hz]


theorem enter_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (8+states) (enterReturn continuation) := by
  have hm := Source284UnaryClear.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases h0 : q=0
  · subst q
    have he : (shiftRow 1 (Source284UnaryClear.table continuation 4 b)).next = some q' := by
      simpa [enterReturn] using hnext
    cases hh : (Source284UnaryClear.table continuation 4 b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hm 4 (by omega) b r hh
      simp [shiftRow,hh] at he
      subst q'; omega
  · have he : (shiftRow 1 (Source284UnaryClear.table continuation (q-1) b)).next = some q' := by
      simpa [enterReturn,h0] using hnext
    cases hh : (Source284UnaryClear.table continuation (q-1) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hm (q-1) (by omega) b r hh
      simp [shiftRow,hh] at he
      subst q'; omega

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (10+states) (table continuation) := by
  have hm := enter_closed states continuation hn hv
  intro q hq b q' hnext
  by_cases hsmall : q < 2
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have he : (shiftRow 2 (enterReturn continuation (q-2) b)).next = some q' := by
      simpa [table,show q ≠ 0 by omega,show q ≠ 1 by omega] using hnext
    cases hh : (enterReturn continuation (q-2) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hm (q-2) (by omega) b r hh
      simp [shiftRow,hh] at he
      subst q'; omega

/-- Encoded unary-record execution of the return rows, with the entire
certificate and scratch stream preserved. -/
theorem source_restore (states : Nat) (continuation : Nat → Bool → Row)
    (m outer stream : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (encode (10+states) (table continuation) 1)
      (Source284Relative.initial (4*push (2*stream+1) (List.replicate m false)) outer) (2*m+4) =
      ⟨pairTape (List.replicate m false) outer,2*stream,active 10⟩ := by
  let start : Config := ⟨outer,4*push (2*stream+1) (List.replicate m false),some 0⟩
  have hi : Valid (10+states) start := by intro q hq; simp [start] at hq; subst q; omega
  have hr := run_toSource (10+states) (table continuation) 1 start (closed states continuation hn hv) hi (2*m+4)
  rw [restore] at hr
  exact hr


namespace Fixtures

def loop (q : Nat) (b : Bool) : Row := ⟨b,false,some q⟩
example : run (table loop) ⟨3,4*push 1 [],some 0⟩ 4 =
    ⟨pairTape [] 3,0,some 10⟩ := by decide +kernel
example : run (table loop) ⟨3,4*push 1 [false],some 0⟩ 6 =
    ⟨pairTape [false] 3,0,some 10⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284NestedReturn
