import Shared.Beeping.NPcoNP.Source284SquareLoopTotal
import Shared.Beeping.NPcoNP.Source284SourceRelocation

/-! Numeric source encoding for the autonomous token-counting loop. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284SquareLoopSource

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)
open Shared.Beeping.NPcoNP.Source284SquareLoop (table)
open Shared.Beeping.NPcoNP.Source284SquareLoopTotal (loopCost)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (88+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases h41 : q=41
  · subst q; simp [table] at hnext; omega
  · by_cases h86 : q=86
    · subst q; simp [table] at hnext; omega
    · by_cases hl : q<88
      · have he : (Source284SquareLoopBase.base q b).next = some q' := by
          simpa [table,h41,h86,hl] using hnext
        have hr := Source284SquareLoopBase.closed q hl b q' he
        omega
      · have he : (shiftRow 88 (continuation (q-88) b)).next = some q' := by
          simpa [table,h41,h86,hl] using hnext
        cases hh : (continuation (q-88) b).next with
        | none => simp [shiftRow,hh] at he
        | some r =>
          have hr := hv (q-88) (by omega) b r hh
          simp [shiftRow,hh] at he
          subst q'; omega

/-- The encoded numeric source autonomously consumes the unmarked outer
tokens, reaches exhaustion, and executes its continuation. -/
theorem source_loop_then (states : Nat) (continuation : Nat → Bool → Row)
    (r m k n : Nat) (w : List Bool) (certificate higher fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (encode (88+states) (table continuation) 1)
      (Source284Relative.initial (2*flipped w (counter n higher))
        (pairTape (List.replicate m false)
          (pairTape (List.replicate k true ++ List.replicate r false) certificate)))
      (loopCost r m k n w.length+fuel) =
    Source284SourceRelocation.lift 88
      (Source284Relative.run (encode states continuation 1)
        ⟨pairTape (List.replicate m false) (pairTape (List.replicate (k+r) true) certificate),
          2*flipped w (counter (n+r*m) (halves (r*m) higher)),active 0⟩ fuel) := by
  let start : Config := ⟨pairTape (List.replicate m false)
    (pairTape (List.replicate k true ++ List.replicate r false) certificate),2*flipped w (counter n higher),some 0⟩
  have hi : Valid (88+states) start := by intro q hq; simp [start] at hq; subst q; omega
  have hr := run_toSource (88+states) (table continuation) 1 start (closed states continuation hn hv)
    hi (loopCost r m k n w.length+fuel)
  rw [Source284SquareLoopTotal.loop_then,← Source284SourceRelocation.lift_toSource] at hr
  let finish : Config := ⟨pairTape (List.replicate m false) (pairTape (List.replicate (k+r) true) certificate),
    2*flipped w (counter (n+r*m) (halves (r*m) higher)),some 0⟩
  have hf : Valid states finish := by intro q hq; simp [finish] at hq; subst q; exact hn
  have hs := run_toSource states continuation 1 finish hv hf fuel
  rw [← hs] at hr
  exact hr

end Shared.Beeping.NPcoNP.Source284SquareLoopSource
