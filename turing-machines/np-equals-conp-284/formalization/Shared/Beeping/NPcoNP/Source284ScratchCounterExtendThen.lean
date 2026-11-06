import Shared.Beeping.NPcoNP.Source284ScratchCounterExtend

/-! Continue after the paid scratch counter extension without assuming a
halt. This is used to keep a separate unary workspace counter behind the
cutoff initializer's own terminating zero. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284ScratchCounterExtendThen

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)

theorem continuation_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (Source284ScratchCounterExtend.table continuation) (shiftConfig 16 c) fuel =
      shiftConfig 16 (run continuation c fuel) := by
  have hs (d : Config) : shiftConfig 16 d = shiftConfig 4 (shiftConfig 5 (shiftConfig 1 (shiftConfig 6 d))) := by
    cases d with
    | mk left right state => cases state <;> simp [shiftConfig] <;> omega
  rw [hs,Source284ScratchCounterExtend.relocated_run,Source284CounterExtend.relocated_run,
    Source284ScratchCounterSeed.after_relocated_run,Source284ScratchFlipReturn.relocated_run,← hs]

/-- A finite source table adds one marked counter cell and resumes the
continuation at every later clock, retaining the explicit high suffix. -/
theorem extend_then (continuation : Nat → Bool → Row) (w : List Bool)
    (n certificate higher fuel : Nat) :
    run (Source284ScratchCounterExtend.table continuation)
      ⟨certificate,2*flipped w (counter n higher),some 0⟩ (4*w.length+2*n+16+fuel) =
    shiftConfig 16 (run continuation
      ⟨certificate,2*flipped w (counter (n+1) (higher/2)),some 0⟩ fuel) := by
  rw [Source284ScratchScanner.run_add,Source284ScratchCounterExtend.extend_scratch]
  change run (Source284ScratchCounterExtend.table continuation)
    (shiftConfig 16 ⟨certificate,2*flipped w (counter (n+1) (higher/2)),some 0⟩) fuel = _
  exact continuation_run continuation _ fuel

end Shared.Beeping.NPcoNP.Source284ScratchCounterExtendThen
