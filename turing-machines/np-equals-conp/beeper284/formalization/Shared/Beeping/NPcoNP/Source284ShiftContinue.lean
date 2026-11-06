import Shared.Beeping.NPcoNP.Source284ScratchShiftCycle

/-! Exact continuation form for one paid scratch-stream shift. -/
namespace Shared.Beeping.NPcoNP.Source284ShiftContinue

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

theorem cycle_then (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail fuel : Nat) :
    run (Source284ScratchShiftCycle.table continuation)
      ⟨certificate,2*flipped w tail,some 0⟩ ((4*w.length+7)+fuel) =
    shiftConfig 14 (run continuation ⟨2*certificate,2*flipped w (tail/2),some 0⟩ fuel) := by
  rw [Source284ScratchScanner.run_add,Source284ScratchShiftCycle.cycle_frame]
  change run (Source284ScratchShiftCycle.table continuation)
    (shiftConfig 14 ⟨2*certificate,2*flipped w (tail/2),some 0⟩) fuel = _
  exact Source284ScratchShiftCycle.relocated_run continuation _ fuel

end Shared.Beeping.NPcoNP.Source284ShiftContinue
