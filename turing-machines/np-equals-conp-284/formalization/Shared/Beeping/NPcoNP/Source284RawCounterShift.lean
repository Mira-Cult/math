import Shared.Beeping.NPcoNP.Source284RawCounterWorkspace
import Shared.Beeping.NPcoNP.Source284CountedShift

/-! An explicit paid handoff connects the raw-input counter builder to the
counter-controlled scratch shifter. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284RawCounterShift

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig shiftRow)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

/-- Exhaustion enters state 1; two real turns restore the head and enter the
counter shifter. -/
def adapter (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 1 then ⟨b,true,some 0⟩
  else if q = 0 then ⟨b,true,some 2⟩
  else shiftRow 2 (Source284CountedShift.table continuation (q-2) b)

theorem adapter_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (23+states) (adapter continuation) := by
  have hc := Source284CountedShift.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases hs : q < 2
  · interval_cases q <;> simp [adapter] at hnext <;> omega
  · have ht : (shiftRow 2 (Source284CountedShift.table continuation (q-2) b)).next = some q' := by
      simpa [adapter,show q ≠ 0 by omega,show q ≠ 1 by omega] using hnext
    cases he : (Source284CountedShift.table continuation (q-2) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have hr := hc (q-2) (by omega) b r he
      simp [shiftRow,he] at ht
      subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    adapter continuation (2+q) b = shiftRow 2 (Source284CountedShift.table continuation q b) := by
  simp [adapter,show 2+q ≠ 1 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (adapter continuation) (shiftConfig 2 c) =
      shiftConfig 2 (step (Source284CountedShift.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (adapter continuation) (shiftConfig 2 c) fuel =
      shiftConfig 2 (run (Source284CountedShift.table continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem enter (continuation : Nat → Bool → Row) (left right : Nat) :
    run (adapter continuation) ⟨left,right,some 1⟩ 2 = ⟨left,right,some 2⟩ := by
  simp [run,step,adapter,bit,Nat.testBit_zero] <;> split_ifs <;> omega

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284RawCounterWorkspace.description (23+states) (adapter continuation)

def cost (m k width : Nat) : Nat :=
  Source284RawCounterWorkspace.cost m k width + 2 + (m+1)*(4*width+7)

/-- The actual encoded source packs the raw input, prepares its unary
counter, uses it to insert `m+1` zero cells on the opposite half, and then
runs the supplied continuation. The token tape remains an explicit premise. -/
theorem source_shift_then (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (m k certificate suffix fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix)
        (pairTape (List.replicate k true ++ List.replicate m false) certificate))
      (cost m k w.length+fuel) =
      toSource (shiftConfig 204 (run continuation
        ⟨2^(m+1)*pairTape (List.replicate (k+m) true) certificate,
          2*flipped w (Source284TokenCounterLoop.halves m ((suffix/4)/2)),some 0⟩ fuel)) := by
  have hc := adapter_closed states continuation hn hv
  have hs := Source284RawCounterWorkspace.source_workspace_then (23+states) (adapter continuation)
    w m k certificate suffix (2+((m+1)*(4*w.length+7)+fuel)) (by omega) hc
  have ht : cost m k w.length+fuel = Source284RawCounterWorkspace.cost m k w.length +
      (2+((m+1)*(4*w.length+7)+fuel)) := by simp [cost]; omega
  rw [ht]
  rw [Source284ScratchFlipReturn.run_add,enter] at hs
  change Source284Relative.run (description states continuation) _ _ =
    toSource (shiftConfig 181 (run (adapter continuation)
      (shiftConfig 2 ⟨pairTape (List.replicate (k+m) true) certificate,
        2*flipped w (Source284CountedShift.counter m
          (Source284TokenCounterLoop.halves m ((suffix/4)/2))),some 0⟩) _)) at hs
  rw [relocated_run,Source284CountedShift.countdown_after] at hs
  repeat rw [Source284SourceRelocation.shiftConfig_add] at hs
  exact hs

/-- Exact configuration at the start of the shifted continuation. -/
theorem source_shift (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (m k certificate suffix : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix)
        (pairTape (List.replicate k true ++ List.replicate m false) certificate))
      (cost m k w.length) =
      ⟨2^(m+1)*pairTape (List.replicate (k+m) true) certificate,
        2*flipped w (Source284TokenCounterLoop.halves m ((suffix/4)/2)),active 204⟩ := by
  have h := source_shift_then states continuation w m k certificate suffix 0 hn hv
  simpa [run,shiftConfig,toSource,nextState,active] using h

/-- Every numeric input has such a run. The produced opposite tape half has
at least `m+1` low zero cells, without assuming its high data are zero. -/
theorem source_total_shift (states : Nat) (continuation : Nat → Bool → Row)
    (input m k certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix left right : Nat),
      Source284Parser.encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (description states continuation)
        (Source284Relative.initial input
          (pairTape (List.replicate k true ++ List.replicate m false) certificate))
        (cost m k (Source284Parser.length input)) = ⟨left,right,active 204⟩ ∧
      2^(m+1) ∣ left := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,2^(m+1)*pairTape (List.replicate (k+m) true) certificate,
    2*flipped w (Source284TokenCounterLoop.halves m ((suffix/4)/2)),hw,hlen.symm,?_,?_⟩
  · rw [hlen,← hw]
    exact source_shift states continuation w m k certificate suffix hn hv
  · exact dvd_mul_right _ _

theorem cost_formula (m k width : Nat) :
    cost m k width = 2*width*width+22*width+30+
      (3*m*m+m*(4*k+4*width+25)+4*k+8)+2+(m+1)*(4*width+7) := by
  rw [cost,Source284RawCounterWorkspace.cost_formula]

namespace Fixtures

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial 0 2) 47 = ⟨4,0,active 204⟩ := by
  simpa [cost_formula,Source284Parser.encodeFrame,pairTape,Source284PayloadLoop.scratch,
    flipped,Source284TokenCounterLoop.halves] using
    source_shift states continuation [] 0 0 0 0 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial 0 8) 82 = ⟨36,0,active 204⟩ := by
  simpa [cost_formula,Source284Parser.encodeFrame,pairTape,Source284PayloadLoop.scratch,
    flipped,Source284TokenCounterLoop.halves,bit] using
    source_shift states continuation [] 1 0 0 0 hn hv

end Fixtures

end Shared.Beeping.NPcoNP.Source284RawCounterShift
