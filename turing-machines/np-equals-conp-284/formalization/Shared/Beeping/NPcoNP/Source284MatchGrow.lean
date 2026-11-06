import Shared.Beeping.NPcoNP.Source284MatchReset
import Shared.Beeping.NPcoNP.Source284ScratchShiftCycle

/-! A paid retry preparation: reset both marked tapes, then run exactly two
finite scratch-shift cycles to add one zero unary pair. The two overwritten
high-suffix cells are explicitly accounted for. -/
namespace Shared.Beeping.NPcoNP.Source284MatchGrow

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284MatchReset.table (Source284ScratchShiftCycle.repeatTable 2 continuation)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (46+states) (table continuation) := by
  have hs := Source284ScratchShiftCycle.repeat_closed 2 states continuation hn hv
  have hr := Source284MatchReset.closed (14*2+states)
    (Source284ScratchShiftCycle.repeatTable 2 continuation) (by omega) hs
  have he : 18+(14*2+states) = 46+states := by omega
  rw [he] at hr
  exact hr

theorem add_zero_pair (n certificate : Nat) :
    2^2*pairTape (List.replicate n false) certificate =
      pairTape (List.replicate (n+1) false) certificate := by
  simp [pairTape,Source284PayloadLoop.scratch,List.replicate_succ,bit]

/-- After clearing arbitrary unary marks and the marked payload prefix, two
paid shifts grow the unary side by one pair, preserving all payload bits and
the certificate. The high suffix is divided by four. -/
theorem reset_grow (continuation : Nat → Bool → Row) (tokens xs rest : List Bool)
    (certificate tail : Nat) :
    run (table continuation)
      ⟨pairTape tokens certificate,2*zeros xs (flipped (rest++[false]) tail),some 0⟩
      (4*tokens.length+12*(xs.length+rest.length)+40) =
    ⟨pairTape (List.replicate (tokens.length+1) false) certificate,
      2*flipped ((xs++rest)++[false]) (tail/4),some 46⟩ := by
  let w := (xs++rest)++[false]
  have hw : w.length = xs.length+rest.length+1 := by simp [w]; omega
  have ht : 4*tokens.length+12*(xs.length+rest.length)+40 =
      ((4*tokens.length+6)+(4*(xs.length+rest.length)+12)) + 2*(4*w.length+7) := by rw [hw]; ring
  rw [ht,run_add]
  change run (Source284MatchReset.table (Source284ScratchShiftCycle.repeatTable 2 continuation))
    (run (Source284MatchReset.table (Source284ScratchShiftCycle.repeatTable 2 continuation)) _ _) _ = _
  rw [Source284MatchReset.reset]
  change run (Source284UnaryClear.table (Source284PayloadReset.table (Source284ScratchShiftCycle.repeatTable 2 continuation)))
    (shiftConfig 7 (shiftConfig 5 (shiftConfig 6
      ⟨pairTape (List.replicate tokens.length false) certificate,2*flipped w tail,some 0⟩))) _ = _
  rw [Source284UnaryClear.relocated_run,Source284PayloadReset.relocated_run,
    Source284ScratchFlipReturn.relocated_run,Source284ScratchShiftCycle.repeat_run,add_zero_pair]
  rfl

end Shared.Beeping.NPcoNP.Source284MatchGrow
