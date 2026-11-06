import Shared.Beeping.NPcoNP.Source284ScratchCounterExtend

/-! Seed a counter beyond an already flipped, self-delimited scratch stream. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284FlippedCounterSeed

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (push flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284ScratchCounterSeed (afterSeed)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,false,some 1⟩
  else if q = 1 then ⟨b,false,some 2⟩
  else if q = 2 then ⟨b,!b,some (if b then 1 else 3)⟩
  else if q = 3 then ⟨b,true,some 4⟩
  else shiftRow 4 (Source284CounterSeed.table (afterSeed continuation) (q-4) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (16+states) (table continuation) := by
  have hc := Source284CounterSeed.closed (7+states) (afterSeed continuation) (by omega)
    (Source284ScratchCounterSeed.afterSeed_closed states continuation hn hv)
  intro q hq b q' hnext
  by_cases hsmall : q < 4
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have he : (shiftRow 4 (Source284CounterSeed.table (afterSeed continuation) (q-4) b)).next = some q' := by
      simpa [table,show q ≠ 0 by omega,show q ≠ 1 by omega,
        show q ≠ 2 by omega,show q ≠ 3 by omega] using hnext
    cases hh : (Source284CounterSeed.table (afterSeed continuation) (q-4) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hc (q-4) (by omega) b r hh
      simp [shiftRow,hh] at he
      subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (4+q) b = shiftRow 4 (Source284CounterSeed.table (afterSeed continuation) q b) := by
  simp [table,show 4+q ≠ 1 by omega,show 4+q ≠ 2 by omega,show 4+q ≠ 3 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 4 c) =
      shiftConfig 4 (step (Source284CounterSeed.table (afterSeed continuation)) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 4 c) fuel =
      shiftConfig 4 (run (Source284CounterSeed.table (afterSeed continuation)) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem initial (continuation : Nat → Bool → Row) (left right : Nat) :
    step (table continuation) ⟨left,2*right,some 0⟩ = ⟨2*left,right,some 1⟩ := by
  simp [step,table,bit]

theorem payload_pair (continuation : Nat → Bool → Row) (left tail : Nat) (b : Bool) :
    run (table continuation) ⟨left,bit b+2+4*tail,some 1⟩ 2 =
      ⟨4*left+2*bit b+1,tail,some 1⟩ := by
  have h1 : step (table continuation) ⟨left,bit b+2+4*tail,some 1⟩ =
      ⟨2*left+bit b,2*tail+1,some 2⟩ := by
    cases b <;> simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have h2 : step (table continuation) ⟨2*left+bit b,2*tail+1,some 2⟩ =
      ⟨2*(2*left+bit b)+1,tail,some 1⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod] <;> omega
  rw [Source284HardwireTable.run_front,h1,Source284HardwireTable.run_front,h2]
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
    rw [ht,run_add]
    change run (table continuation)
      (run (table continuation) ⟨left,bit b+2+4*flipped bs tail,some 1⟩ 2) _ = _
    rw [payload_pair,ih]
    rfl

/-- The scan and seed preserve the payload and certificate; the first high
suffix bit is overwritten as a paid counter terminator. -/
theorem seed_scratch (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate suffix : Nat) :
    run (table continuation) ⟨certificate,2*flipped w suffix,some 0⟩ (4*w.length+14) =
      ⟨certificate,2*flipped w (counter 0 (suffix/2)),some 16⟩ := by
  have ht : 4*w.length+14 = 1+((2*w.length+3)+(4+(1+(2*w.length+5)))) := by omega
  rw [ht,run_add]
  change run (table continuation) (step (table continuation)
    ⟨certificate,2*flipped w suffix,some 0⟩) _ = _
  rw [initial,run_add,scan]
  change run (table continuation) (shiftConfig 4
    ⟨2*push (2*certificate) w,2*suffix,some 0⟩) _ = _
  rw [relocated_run,run_add,Source284CounterSeed.seed]
  change shiftConfig 4 (run (Source284CounterSeed.table (afterSeed continuation))
    (shiftConfig 2 (shiftConfig 3 ⟨2*push (2*certificate) w,2*counter 0 (suffix/2),some 0⟩)) _) = _
  rw [Source284CounterSeed.relocated_run]
  change shiftConfig 4 (shiftConfig 2 (run (Source284OrientationHandoff.table 0 (afterSeed continuation))
    (shiftConfig 3 ⟨2*push (2*certificate) w,2*counter 0 (suffix/2),some 0⟩) _)) = _
  rw [Source284OrientationHandoff.relocated_run,run_add]
  change shiftConfig 4 (shiftConfig 2 (shiftConfig 3 (run (afterSeed continuation)
    (step (afterSeed continuation) ⟨2*push (2*certificate) w,2*counter 0 (suffix/2),some 0⟩) _))) = _
  have hstep : step (afterSeed continuation)
      ⟨2*push (2*certificate) w,2*counter 0 (suffix/2),some 0⟩ =
      shiftConfig 1 ⟨4*push (2*certificate) w,counter 0 (suffix/2),some 0⟩ := by
    simp [step,afterSeed,shiftConfig,bit,Nat.testBit_zero]
    omega
  rw [hstep,Source284ScratchCounterSeed.after_relocated_run,Source284ScratchFlipReturn.return_frame]
  rfl

theorem continuation_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 16 c) fuel = shiftConfig 16 (run continuation c fuel) := by
  rw [← Source284ScratchCounterSeed.shift_nested c]
  rw [relocated_run,Source284CounterSeed.relocated_run,Source284OrientationHandoff.relocated_run,
    Source284ScratchCounterSeed.after_relocated_run,Source284ScratchFlipReturn.relocated_run,
    Source284ScratchCounterSeed.shift_nested]

theorem seed_then (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate suffix fuel : Nat) :
    run (table continuation) ⟨certificate,2*flipped w suffix,some 0⟩ (4*w.length+14+fuel) =
      shiftConfig 16 (run continuation ⟨certificate,2*flipped w (counter 0 (suffix/2)),some 0⟩ fuel) := by
  rw [run_add,seed_scratch]
  change run (table continuation)
    (shiftConfig 16 ⟨certificate,2*flipped w (counter 0 (suffix/2)),some 0⟩) fuel = _
  exact continuation_run continuation _ fuel

end Shared.Beeping.NPcoNP.Source284FlippedCounterSeed
