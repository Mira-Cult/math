import Shared.Beeping.NPcoNP.Source284ScratchCounterSeed
import Shared.Beeping.NPcoNP.Source284CounterExtend

/-! Reach the counter at the far end of a self-delimited flipped scratch
stream, extend it once, and return to the original boundary. All source
steps and the overwritten high-suffix bit are accounted for. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284ScratchCounterExtend

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (push flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284ScratchCounterSeed (afterSeed)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,false,some 1⟩
  else if q = 1 then ⟨b,false,some 2⟩
  else if q = 2 then ⟨b,!b,some (if b then 1 else 3)⟩
  else if q = 3 then ⟨b,true,some 4⟩
  else shiftRow 4 (Source284CounterExtend.table (afterSeed continuation) (q-4) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (16+states) (table continuation) := by
  have hc := Source284CounterExtend.closed (7+states) (afterSeed continuation) (by omega)
    (Source284ScratchCounterSeed.afterSeed_closed states continuation hn hv)
  intro q hq b q' hnext
  by_cases hsmall : q < 4
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have he : (shiftRow 4 (Source284CounterExtend.table (afterSeed continuation) (q-4) b)).next = some q' := by
      simpa [table,show q ≠ 0 by omega,show q ≠ 1 by omega,
        show q ≠ 2 by omega,show q ≠ 3 by omega] using hnext
    cases hh : (Source284CounterExtend.table (afterSeed continuation) (q-4) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hc (q-4) (by omega) b r hh
      simp [shiftRow,hh] at he
      subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (4+q) b = shiftRow 4 (Source284CounterExtend.table (afterSeed continuation) q b) := by
  simp [table,show 4+q ≠ 1 by omega,show 4+q ≠ 2 by omega,show 4+q ≠ 3 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 4 c) =
      shiftConfig 4 (step (Source284CounterExtend.table (afterSeed continuation)) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 4 c) fuel =
      shiftConfig 4 (run (Source284CounterExtend.table (afterSeed continuation)) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem initial (continuation : Nat → Bool → Row) (left right : Nat) :
    step (table continuation) ⟨left,2*right,some 0⟩ = ⟨2*left,right,some 1⟩ := by
  simp [step,table,bit]

theorem payload_step (continuation : Nat → Bool → Row) (left tail : Nat) (b : Bool) :
    step (table continuation) ⟨left,bit b+2+4*tail,some 1⟩ =
      ⟨2*left+bit b,2*tail+1,some 2⟩ := by
  cases b <;> simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega

theorem marker_one (continuation : Nat → Bool → Row) (left tail : Nat) :
    step (table continuation) ⟨left,2*tail+1,some 2⟩ = ⟨2*left+1,tail,some 1⟩ := by
  simp [step,table,bit,Nat.testBit_zero,Nat.add_mod] <;> omega

theorem payload_pair (continuation : Nat → Bool → Row) (left tail : Nat) (b : Bool) :
    run (table continuation) ⟨left,bit b+2+4*tail,some 1⟩ 2 =
      ⟨4*left+2*bit b+1,tail,some 1⟩ := by
  rw [Source284HardwireTable.run_front,payload_step,Source284HardwireTable.run_front,marker_one]
  simp only [run]
  congr 1 <;> omega

theorem terminator (continuation : Nat → Bool → Row) (left tail : Nat) :
    run (table continuation) ⟨left,4*tail,some 1⟩ 3 =
      ⟨2*left,2*tail,some 4⟩ := by
  have h1 : step (table continuation) ⟨left,4*tail,some 1⟩ = ⟨2*left,2*tail,some 2⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega
  have h2 : step (table continuation) ⟨2*left,2*tail,some 2⟩ = ⟨2*tail,2*left,some 3⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod]
  have h3 : step (table continuation) ⟨2*tail,2*left,some 3⟩ = ⟨2*left,2*tail,some 4⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod]
  rw [Source284HardwireTable.run_front,h1,Source284HardwireTable.run_front,h2,
    Source284HardwireTable.run_front,h3]
  rfl

theorem scan (continuation : Nat → Bool → Row) (w : List Bool) (left tail : Nat) :
    run (table continuation) ⟨left,flipped w tail,some 1⟩ (2*w.length+3) =
      ⟨2*push left w,2*tail,some 4⟩ := by
  induction w generalizing left with
  | nil => simpa [flipped,push] using terminator continuation left tail
  | cons b bs ih =>
    have ht : 2*(b::bs).length+3 = 2+(2*bs.length+3) := by simp; omega
    rw [ht,Source284ScratchScanner.run_add]
    change run (table continuation)
      (run (table continuation) ⟨left,bit b+2+4*flipped bs tail,some 1⟩ 2) _ = _
    rw [payload_pair,ih]
    rfl

/-- The counter extension is performed at the actual high-suffix boundary;
the return pass preserves the entire certificate and the payload. -/
theorem extend_scratch (continuation : Nat → Bool → Row) (w : List Bool)
    (n certificate higher : Nat) :
    run (table continuation) ⟨certificate,2*flipped w (counter n higher),some 0⟩
      (4*w.length+2*n+16) =
      ⟨certificate,2*flipped w (counter (n+1) (higher/2)),some 16⟩ := by
  have ht : 4*w.length+2*n+16 = 1+((2*w.length+3)+((2*n+6)+(1+(2*w.length+5)))) := by omega
  rw [ht,Source284ScratchScanner.run_add]
  change run (table continuation) (step (table continuation)
    ⟨certificate,2*flipped w (counter n higher),some 0⟩) _ = _
  rw [initial,Source284ScratchScanner.run_add,scan]
  change run (table continuation) (shiftConfig 4
    ⟨2*push (2*certificate) w,2*counter n higher,some 0⟩) _ = _
  rw [relocated_run,Source284ScratchScanner.run_add,Source284CounterExtend.extend]
  change shiftConfig 4 (run (Source284CounterExtend.table (afterSeed continuation))
    (shiftConfig 5 ⟨2*push (2*certificate) w,2*counter (n+1) (higher/2),some 0⟩) _) = _
  rw [Source284CounterExtend.relocated_run,Source284ScratchScanner.run_add]
  change shiftConfig 4 (shiftConfig 5 (run (afterSeed continuation)
    (step (afterSeed continuation)
      ⟨2*push (2*certificate) w,2*counter (n+1) (higher/2),some 0⟩) _)) = _
  have hstep : step (afterSeed continuation)
      ⟨2*push (2*certificate) w,2*counter (n+1) (higher/2),some 0⟩ =
      shiftConfig 1 ⟨4*push (2*certificate) w,counter (n+1) (higher/2),some 0⟩ := by
    simp [step,afterSeed,shiftConfig,bit,Nat.testBit_zero]
    omega
  rw [hstep,Source284ScratchCounterSeed.after_relocated_run,Source284ScratchFlipReturn.return_frame]
  rfl


/-- The final return row before the head is turned back to the boundary. -/
theorem return_pre (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail : Nat) :
    run (Source284ScratchFlipReturn.table continuation)
      ⟨4*push (2*certificate) w,tail,some 0⟩ (2*w.length+4) =
      ⟨2*flipped w tail,certificate,some 5⟩ := by
  have ht : 2*w.length+4 = 3+(2*w.length)+1 := by omega
  rw [ht,Source284ScratchFlipReturn.run_add,Source284ScratchFlipReturn.run_add,
    Source284ScratchFlipReturn.turn_start,Source284ScratchFlipReturn.reverse_pairs,
    Source284ScratchFlipReturn.raw_flipped]
  simp [run,step,Source284ScratchFlipReturn.table,bit,Nat.testBit_zero]

/-- The exact last-row configuration of the scratch extension, before the
final turn that restores the original boundary. -/
theorem extend_scratch_pre (continuation : Nat → Bool → Row) (w : List Bool)
    (n certificate higher : Nat) :
    run (table continuation) ⟨certificate,2*flipped w (counter n higher),some 0⟩
      (4*w.length+2*n+15) =
      ⟨2*flipped w (counter (n+1) (higher/2)),certificate,some 15⟩ := by
  have ht : 4*w.length+2*n+15 = 1+((2*w.length+3)+((2*n+6)+(1+(2*w.length+4)))) := by omega
  rw [ht,Source284ScratchScanner.run_add]
  change run (table continuation) (step (table continuation)
    ⟨certificate,2*flipped w (counter n higher),some 0⟩) _ = _
  rw [initial,Source284ScratchScanner.run_add,scan]
  change run (table continuation) (shiftConfig 4
    ⟨2*push (2*certificate) w,2*counter n higher,some 0⟩) _ = _
  rw [relocated_run,Source284ScratchScanner.run_add,Source284CounterExtend.extend]
  change shiftConfig 4 (run (Source284CounterExtend.table (afterSeed continuation))
    (shiftConfig 5 ⟨2*push (2*certificate) w,2*counter (n+1) (higher/2),some 0⟩) _) = _
  rw [Source284CounterExtend.relocated_run,Source284ScratchScanner.run_add]
  change shiftConfig 4 (shiftConfig 5 (run (afterSeed continuation)
    (step (afterSeed continuation)
      ⟨2*push (2*certificate) w,2*counter (n+1) (higher/2),some 0⟩) _)) = _
  have hstep : step (afterSeed continuation)
      ⟨2*push (2*certificate) w,2*counter (n+1) (higher/2),some 0⟩ =
      shiftConfig 1 ⟨4*push (2*certificate) w,counter (n+1) (higher/2),some 0⟩ := by
    simp [step,afterSeed,shiftConfig,bit,Nat.testBit_zero]
    omega
  rw [hstep,Source284ScratchCounterSeed.after_relocated_run,return_pre]
  rfl

end Shared.Beeping.NPcoNP.Source284ScratchCounterExtend
