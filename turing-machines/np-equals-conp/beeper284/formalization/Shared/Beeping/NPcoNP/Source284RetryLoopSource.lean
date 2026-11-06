import Shared.Beeping.NPcoNP.Source284RetryLoopComplete

/-! Numeric source encoding of autonomous retries from a prepared tape.
The final configuration includes the exact paid dispatch movement. -/
namespace Shared.Beeping.NPcoNP.Source284RetryLoopSource

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  encode (97+states) (Source284RetryLoop.table continuation) 1

theorem source_complete (states : Nat) (continuation : Nat → Bool → Row) (k : Nat) (w : List Bool)
    (certificate tail : Nat) (hn : 2 ≤ states) (hv : Closed states continuation) (hle : k ≤ w.length) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (2*flipped (w++[false]) tail) (pairTape (List.replicate k false) certificate))
      (Source284RetryLoopComplete.totalCost k w.length) =
    ⟨2*pairTape (List.replicate w.length true) certificate,
      zeros w (flipped [false] (tail/4^(w.length-k))),active 98⟩ := by
  let c : Config := ⟨pairTape (List.replicate k false) certificate,2*flipped (w++[false]) tail,some 0⟩
  have hc : Valid (97+states) c := by intro q hq; simp [c] at hq; subst q; omega
  have hr := run_toSource (97+states) (Source284RetryLoop.table continuation) 1 c
    (Source284RetryLoop.closed states continuation hn hv) hc (Source284RetryLoopComplete.totalCost k w.length)
  change Source284Relative.run (description states continuation)
    (Source284Relative.initial (2*flipped (w++[false]) tail) (pairTape (List.replicate k false) certificate)) _ = _ at hr
  rw [hr]
  dsimp only [c]
  rw [Source284RetryLoopComplete.complete continuation k w certificate tail hle]
  rfl

theorem source_after (states : Nat) (continuation : Nat → Bool → Row) (mode : Nat)
    (left right fuel : Nat) (hn : 2 ≤ states) (hm : mode < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) ⟨left,right,active (97+mode)⟩ fuel =
      toSource (shiftConfig 97 (run continuation ⟨left,right,some mode⟩ fuel)) := by
  let c : Config := ⟨left,right,some mode⟩
  have hc : Valid (97+states) (shiftConfig 97 c) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := run_toSource (97+states) (Source284RetryLoop.table continuation) 1 (shiftConfig 97 c)
    (Source284RetryLoop.closed states continuation hn hv) hc fuel
  change Source284Relative.run (description states continuation) ⟨left,right,active (97+mode)⟩ fuel = _ at hr
  rw [hr,Source284RetryLoop.relocated_run]

end Shared.Beeping.NPcoNP.Source284RetryLoopSource
