import Shared.Beeping.NPcoNP.Source284UnaryMarkOne

/-! Numeric source-table binding for the finite mark-or-exhaust operation.
The pair sequence is supplied on tape. No autonomous comparison with the
payload or handoff from the runway loop is asserted. -/
set_option maxHeartbeats 1000000

namespace Shared.Beeping.NPcoNP.Source284UnaryMarkOneSource

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  encode (12+states) (Source284UnaryMarkOne.table continuation) 1

/-- The encoded source changes exactly the first unmarked token and selects
continuation state zero. -/
theorem source_mark (states : Nat) (continuation : Nat → Bool → Row)
    (k : Nat) (rest : List Bool) (certificate stream : Nat)
    (hn : 2 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (2*stream) (pairTape (List.replicate k true ++ false::rest) certificate))
      (4*k+6) =
      ⟨pairTape (List.replicate k true ++ true::rest) certificate,2*stream,active 12⟩ := by
  let c : Config := ⟨pairTape (List.replicate k true ++ false::rest) certificate,2*stream,some 0⟩
  have hvalid : Valid (12+states) c := by
    intro q hq
    simp [c] at hq
    subst q
    omega
  have hr := run_toSource (12+states) (Source284UnaryMarkOne.table continuation) 1 c
    (Source284UnaryMarkOne.closed states continuation hn hv) hvalid (4*k+6)
  change Source284Relative.run (description states continuation)
    (Source284Relative.initial (2*stream) (pairTape (List.replicate k true ++ false::rest) certificate)) _ = _ at hr
  rw [hr]
  dsimp only [c]
  rw [Source284UnaryMarkOne.mark_first]
  rfl

/-- If every token was already marked, the encoded source restores the tape
and selects continuation state one. -/
theorem source_exhausted (states : Nat) (continuation : Nat → Bool → Row)
    (k certificate stream : Nat) (hn : 2 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (2*stream) (pairTape (List.replicate k true) certificate)) (4*k+6) =
      ⟨pairTape (List.replicate k true) certificate,2*stream,active 13⟩ := by
  let c : Config := ⟨pairTape (List.replicate k true) certificate,2*stream,some 0⟩
  have hvalid : Valid (12+states) c := by
    intro q hq
    simp [c] at hq
    subst q
    omega
  have hr := run_toSource (12+states) (Source284UnaryMarkOne.table continuation) 1 c
    (Source284UnaryMarkOne.closed states continuation hn hv) hvalid (4*k+6)
  change Source284Relative.run (description states continuation)
    (Source284Relative.initial (2*stream) (pairTape (List.replicate k true) certificate)) _ = _ at hr
  rw [hr]
  dsimp only [c]
  rw [Source284UnaryMarkOne.all_marked]
  rfl

/-- From either selected mode, continuation steps are part of the same
encoded source run, with the twelve-state relocation charged explicitly. -/
theorem source_after (states : Nat) (continuation : Nat → Bool → Row)
    (mode : Nat) (hm : mode < states) (left right fuel : Nat)
    (hn : 2 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) ⟨left,right,active (12+mode)⟩ fuel =
      toSource (shiftConfig 12 (run continuation ⟨left,right,some mode⟩ fuel)) := by
  let c : Config := ⟨left,right,some mode⟩
  have hvalid : Valid (12+states) (shiftConfig 12 c) := by
    intro q hq
    simp [shiftConfig,c] at hq
    subst q
    omega
  have hr := run_toSource (12+states) (Source284UnaryMarkOne.table continuation) 1 (shiftConfig 12 c)
    (Source284UnaryMarkOne.closed states continuation hn hv) hvalid fuel
  change Source284Relative.run (description states continuation) ⟨left,right,active (12+mode)⟩ fuel = _ at hr
  rw [hr,Source284UnaryMarkOne.relocated_run]

/-- The success branch and all subsequent continuation steps run in the same
encoded table; no external handoff or time is omitted. -/
theorem source_mark_then (states : Nat) (continuation : Nat → Bool → Row)
    (k : Nat) (rest : List Bool) (certificate stream fuel : Nat)
    (hn : 2 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (2*stream) (pairTape (List.replicate k true ++ false::rest) certificate))
      (4*k+6+fuel) =
      toSource (shiftConfig 12 (run continuation
        ⟨pairTape (List.replicate k true ++ true::rest) certificate,2*stream,some 0⟩ fuel)) := by
  rw [Source284Relative.run_add_clock,source_mark states continuation k rest certificate stream hn hv]
  change Source284Relative.run (description states continuation)
    ⟨pairTape (List.replicate k true ++ true::rest) certificate,2*stream,active (12+0)⟩ fuel = _
  exact source_after states continuation 0 (by omega) _ _ fuel hn hv

/-- The exhausted branch similarly runs continuation state one. -/
theorem source_exhausted_then (states : Nat) (continuation : Nat → Bool → Row)
    (k certificate stream fuel : Nat) (hn : 2 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (2*stream) (pairTape (List.replicate k true) certificate))
      (4*k+6+fuel) =
      toSource (shiftConfig 12 (run continuation
        ⟨pairTape (List.replicate k true) certificate,2*stream,some 1⟩ fuel)) := by
  rw [Source284Relative.run_add_clock,source_exhausted states continuation k certificate stream hn hv]
  change Source284Relative.run (description states continuation)
    ⟨pairTape (List.replicate k true) certificate,2*stream,active (12+1)⟩ fuel = _
  exact source_after states continuation 1 (by omega) _ _ fuel hn hv

namespace Fixtures
example (states : Nat) (continuation : Nat → Bool → Row) (hn : 2 ≤ states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 22 480) 6 =
      ⟨481,22,active 12⟩ := by
  simpa [pairTape,Source284PayloadLoop.scratch,bit] using
    source_mark states continuation 0 [false] 7 11 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 2 ≤ states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 22 485) 14 =
      ⟨485,22,active 13⟩ := by
  simpa [pairTape,Source284PayloadLoop.scratch,bit] using
    source_exhausted states continuation 2 7 11 hn hv
end Fixtures

end Shared.Beeping.NPcoNP.Source284UnaryMarkOneSource
