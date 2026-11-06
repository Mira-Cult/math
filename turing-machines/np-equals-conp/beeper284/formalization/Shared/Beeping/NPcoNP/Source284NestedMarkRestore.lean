import Shared.Beeping.NPcoNP.Source284NestedReturn
import Shared.Beeping.NPcoNP.Source284SourceRelocation

/-! Compose the successful outer mark with a paid return across the inner
block in one finite table. Exhaustion is proved separately by NestedMarker;
its own return/dispatch remains a separate obligation. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284NestedMarkRestore

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

theorem shift_nested (c : Config) :
    shiftConfig 1 (shiftConfig 3 (shiftConfig 1 (shiftConfig 12 c))) = shiftConfig 17 c := by
  cases c with
  | mk left right state => cases state <;> simp [shiftConfig] <;> omega

theorem continuation_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (Source284NestedMarker.table continuation) (shiftConfig 17 c) fuel =
      shiftConfig 17 (run continuation c fuel) := by
  rw [← shift_nested c]
  rw [Source284NestedMarker.scanner_run,Source284ScratchScanner.relocated_run,
    Source284NestedMarker.marker_run,Source284UnaryMarkOne.relocated_run,shift_nested]

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284NestedMarker.table (Source284NestedReturn.table continuation)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (27+states) (table continuation) := by
  have hr := Source284NestedReturn.closed states continuation hn hv
  have hm := Source284NestedMarker.closed (10+states) (Source284NestedReturn.table continuation) (by omega) hr
  have he : 17+(10+states) = 27+states := by omega
  rw [he] at hm
  exact hm

/-- One finite table marks the outer token and restores the inner block,
scratch boundary, and complete arbitrary certificate. -/
theorem mark_restore (continuation : Nat → Bool → Row) (m k : Nat) (rest : List Bool)
    (certificate stream : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true ++ false::rest) certificate),
        2*stream,some 0⟩ (4*m+4*k+12) =
    ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true ++ true::rest) certificate),
      2*stream,some 27⟩ := by
  have ht : 4*m+4*k+12 = (2*(List.replicate m false).length+4*k+8)+(2*m+4) := by simp; omega
  rw [ht,Source284ScratchScanner.run_add]
  unfold table
  rw [Source284NestedMarker.mark_outer]
  change run (Source284NestedMarker.table (Source284NestedReturn.table continuation))
    (shiftConfig 17 ⟨pairTape (List.replicate k true ++ true::rest) certificate,
      4*Source284ScratchScanner.push (2*stream+1) (List.replicate m false),some 0⟩) _ = _
  rw [continuation_run,Source284NestedReturn.restore]
  rfl

theorem source_mark_restore (states : Nat) (continuation : Nat → Bool → Row)
    (m k : Nat) (rest : List Bool) (certificate stream : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (encode (27+states) (table continuation) 1)
      (Source284Relative.initial (2*stream)
        (pairTape (List.replicate m false) (pairTape (List.replicate k true ++ false::rest) certificate)))
      (4*m+4*k+12) =
    ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true ++ true::rest) certificate),
      2*stream,active 27⟩ := by
  let start : Config := ⟨pairTape (List.replicate m false)
    (pairTape (List.replicate k true ++ false::rest) certificate),2*stream,some 0⟩
  have hi : Valid (27+states) start := by intro q hq; simp [start] at hq; subst q; omega
  have hr := run_toSource (27+states) (table continuation) 1 start (closed states continuation hn hv)
    hi (4*m+4*k+12)
  rw [mark_restore] at hr
  exact hr


namespace Fixtures

def loop (q : Nat) (b : Bool) : Row := ⟨b,false,some q⟩
example : run (table loop) ⟨pairTape [] (pairTape [false] 3),0,some 0⟩ 12 =
    ⟨pairTape [] (pairTape [true] 3),0,some 27⟩ := by decide +kernel
example : run (table loop) ⟨pairTape [false] (pairTape [true,false] 3),0,some 0⟩ 20 =
    ⟨pairTape [false] (pairTape [true,true] 3),0,some 27⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284NestedMarkRestore
