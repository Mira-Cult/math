import Shared.Beeping.NPcoNP.Source284TwoSidedWorkspace

/-! Transfer a prepared unary token block into a suffix counter and reset the
block, so the same block can be reused. This is an executable source-table
round; scheduling a runtime-dependent number of rounds is separate. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284ReusableTokenRound

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (consumeTime halves)

def handoff (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284OrientationHandoff.table 0 (Source284UnaryClear.table continuation)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284TokenCounterLoop.table (handoff continuation)

theorem handoff_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (10+states) (handoff continuation) := by
  have hc := Source284UnaryClear.closed states continuation hn hv
  have hh := Source284OrientationHandoff.closed (7+states) 0
    (Source284UnaryClear.table continuation) (by omega) hc
  have he : 3+(7+states) = 10+states := by omega
  rw [he] at hh
  exact hh

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (42+states) (table continuation) := by
  have hh := Source284TokenCounterLoop.closed (10+states) (handoff continuation) (by omega)
    (handoff_closed states continuation hn hv)
  have he : 32+(10+states) = 42+states := by omega
  rw [he] at hh
  exact hh

def roundCost (m n width : Nat) : Nat := consumeTime m 0 n width + 2 + (4*m+6)

theorem roundCost_formula (m n width : Nat) :
    roundCost m n width = 3*m*m + m*(2*n+4*width+29)+16 := by
  simp [roundCost,Source284TokenCounterLoop.consumeTime_formula]
  ring

/-- The marked block is reset, the counter is extended by its length, and
all source steps and changed high-suffix bits are accounted for. -/
theorem round_then (continuation : Nat → Bool → Row) (m n : Nat) (w : List Bool)
    (certificate higher fuel : Nat) :
    run (table continuation) ⟨pairTape (List.replicate m false) certificate,
      2*flipped w (counter n higher),some 0⟩ (roundCost m n w.length+fuel) =
    shiftConfig 42 (run continuation
      ⟨pairTape (List.replicate m false) certificate,
        2*flipped w (counter (n+m) (halves m higher)),some 0⟩ fuel) := by
  have ht : roundCost m n w.length+fuel = consumeTime m 0 n w.length +
      (2+((4*m+6)+fuel)) := by simp [roundCost]; omega
  rw [ht]
  unfold table
  rw [run_add]
  have hc := Source284TokenCounterLoop.consume (handoff continuation) m 0 w n certificate higher
  simp only [List.replicate_zero,List.nil_append,Nat.zero_add] at hc
  rw [hc]
  change run (Source284TokenCounterLoop.table (handoff continuation))
    (shiftConfig 32 ⟨pairTape (List.replicate m true) certificate,
      2*flipped w (counter (n+m) (halves m higher)),some 1⟩) _ = _
  rw [Source284TokenCounterContinue.relocated_run]
  change shiftConfig 32 (run (Source284OrientationHandoff.table 0
    (Source284UnaryClear.table continuation))
    ⟨pairTape (List.replicate m true) certificate,
      2*flipped w (counter (n+m) (halves m higher)),
      some (Source284OrientationHandoff.initialState false)⟩ _) = _
  rw [Source284OrientationHandoff.then_run]
  simp only [Source284OrientationHandoff.normalized,Bool.false_eq_true,ite_false,Prod.fst,Prod.snd]
  rw [run_add]
  have he := Source284UnaryClear.clear continuation (List.replicate m true) certificate
    (flipped w (counter (n+m) (halves m higher)))
  simp only [List.length_replicate] at he
  rw [he]
  change shiftConfig 32 (shiftConfig 3 (run (Source284UnaryClear.table continuation)
    (shiftConfig 7 ⟨pairTape (List.replicate m false) certificate,
      2*flipped w (counter (n+m) (halves m higher)),some 0⟩) fuel)) = _
  rw [Source284UnaryClear.relocated_run]
  repeat rw [Source284SourceRelocation.shiftConfig_add]

/-- The same paid round runs under the actual unary-record encoding. -/
theorem source_round_then (states : Nat) (continuation : Nat → Bool → Row)
    (m n : Nat) (w : List Bool) (certificate higher fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (encode (42+states) (table continuation) 1)
      (Source284Relative.initial (2*flipped w (counter n higher))
        (pairTape (List.replicate m false) certificate)) (roundCost m n w.length+fuel) =
    Source284SourceRelocation.lift 42
      (Source284Relative.run (encode states continuation 1)
        ⟨pairTape (List.replicate m false) certificate,
          2*flipped w (counter (n+m) (halves m higher)),active 0⟩ fuel) := by
  let start : Config := ⟨pairTape (List.replicate m false) certificate,
    2*flipped w (counter n higher),some 0⟩
  have hi : Valid (42+states) start := by intro q hq; simp [start] at hq; subst q; omega
  have hr := run_toSource (42+states) (table continuation) 1 start (closed states continuation hn hv)
    hi (roundCost m n w.length+fuel)
  rw [round_then,← Source284SourceRelocation.lift_toSource] at hr
  let finish : Config := ⟨pairTape (List.replicate m false) certificate,
    2*flipped w (counter (n+m) (halves m higher)),some 0⟩
  have hf : Valid states finish := by intro q hq; simp [finish] at hq; subst q; exact hn
  have hs := run_toSource states continuation 1 finish hv hf fuel
  rw [← hs] at hr
  exact hr

end Shared.Beeping.NPcoNP.Source284ReusableTokenRound
