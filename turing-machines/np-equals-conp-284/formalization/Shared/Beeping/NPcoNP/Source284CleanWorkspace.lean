import Shared.Beeping.NPcoNP.Source284LengthWorkspace
import Shared.Beeping.NPcoNP.Source284UnaryErase

/-! A finite source program converts a unary token tape to contiguous zero
workspace, preserving the arbitrary certificate behind that block. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284CleanWorkspace

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (consumeTime halves)

def handoff (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284OrientationHandoff.table 0
    (Source284UnaryErase.table (Source284CountedShift.table continuation))

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284FlippedCounterSeed.table (Source284TokenCounterLoop.table (handoff continuation))

theorem handoff_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (31+states) (handoff continuation) := by
  have hc := Source284CountedShift.closed states continuation hn hv
  have he := Source284UnaryErase.closed (21+states) (Source284CountedShift.table continuation) (by omega) hc
  have ho := Source284OrientationHandoff.closed (7+(21+states)) 0
    (Source284UnaryErase.table (Source284CountedShift.table continuation)) (by omega) he
  have h : 3+(7+(21+states)) = 31+states := by omega
  rw [h] at ho
  exact ho

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (79+states) (table continuation) := by
  have hh := handoff_closed states continuation hn hv
  have hl := Source284TokenCounterLoop.closed (31+states) (handoff continuation) (by omega) hh
  have hs := Source284FlippedCounterSeed.closed (32+(31+states))
    (Source284TokenCounterLoop.table (handoff continuation)) (by omega) hl
  have he : 16+(32+(31+states)) = 79+states := by omega
  rw [he] at hs
  exact hs

def workCost (m width : Nat) : Nat :=
  (4*width+14) + (consumeTime m 0 0 width +
    (2+((4*m+6)+(m+1)*(4*width+7))))

/-- The temporary token tape and sentinel are erased before the counted
shift, so the returned blank block abuts the original certificate. -/
theorem workspace_then (continuation : Nat → Bool → Row) (m : Nat) (w : List Bool)
    (certificate suffix fuel : Nat) :
    run (table continuation) ⟨pairTape (List.replicate m false) certificate,
      2*flipped w suffix,some 0⟩ (workCost m w.length+fuel) =
    shiftConfig 79 (run continuation
      ⟨2^(3*(m+1))*certificate,2*flipped w (halves m (suffix/2)),some 0⟩ fuel) := by
  have ht : workCost m w.length+fuel = (4*w.length+14) +
      (consumeTime m 0 0 w.length + (2+((4*m+6)+((m+1)*(4*w.length+7)+fuel)))) := by
    simp [workCost]; omega
  rw [ht]
  unfold table
  rw [Source284FlippedCounterSeed.seed_then,run_add]
  have hc := Source284TokenCounterLoop.consume (handoff continuation) m 0 w 0 certificate (suffix/2)
  simp only [List.replicate_zero,List.nil_append,Nat.zero_add] at hc
  rw [hc]
  change shiftConfig 16 (run (Source284TokenCounterLoop.table (handoff continuation))
    (shiftConfig 32 ⟨pairTape (List.replicate m true) certificate,
      2*flipped w (counter m (halves m (suffix/2))),some 1⟩) _) = _
  rw [Source284TokenCounterContinue.relocated_run]
  change shiftConfig 16 (shiftConfig 32 (run
    (Source284OrientationHandoff.table 0
      (Source284UnaryErase.table (Source284CountedShift.table continuation)))
    ⟨pairTape (List.replicate m true) certificate,
      2*flipped w (counter m (halves m (suffix/2))),some (Source284OrientationHandoff.initialState false)⟩ _)) = _
  rw [Source284OrientationHandoff.then_run]
  simp only [Source284OrientationHandoff.normalized,Bool.false_eq_true,ite_false,Prod.fst,Prod.snd]
  have he := Source284UnaryErase.clear_then (Source284CountedShift.table continuation)
    (List.replicate m true) certificate (flipped w (counter m (halves m (suffix/2))))
    ((m+1)*(4*w.length+7)+fuel)
  simp only [List.length_replicate] at he
  rw [he,Source284CountedShift.countdown_after]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  have hp : 2^(m+1)*(4^(m+1)*certificate) = 2^(3*(m+1))*certificate := by
    have h : 4^(m+1) = 2^(2*(m+1)) := by rw [Nat.pow_mul]
    rw [h,← Nat.mul_assoc,← pow_add]
    congr 2 <;> omega
  rw [hp]

theorem workCost_formula (n : Nat) : workCost n (n+1) = 11*n*n+52*n+45 := by
  rw [workCost,Source284TokenCounterLoop.consumeTime_formula]
  ring

end Shared.Beeping.NPcoNP.Source284CleanWorkspace
