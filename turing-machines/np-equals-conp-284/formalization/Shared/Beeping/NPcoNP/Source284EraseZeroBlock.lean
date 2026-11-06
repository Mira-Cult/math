import Shared.Beeping.NPcoNP.Source284ClearOddBoundary
import Shared.Beeping.NPcoNP.Source284ScratchCompactLoop

/-! A fixed source table removes a nonempty zero prefix and its one sentinel
from the certificate side of a protected frame. Each removed cell becomes a
zero on the other side of the frame, with an exact paid transition count. -/
set_option maxRecDepth 4096
namespace Shared.Beeping.NPcoNP.Source284EraseZeroBlock

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284ScratchCompactLoop.table (Source284ClearOddBoundary.table continuation)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (30+states) (table continuation) := by
  have hc := Source284ClearOddBoundary.closed states continuation hn hv
  have hl := Source284ScratchCompactLoop.closed (16+states)
    (Source284ClearOddBoundary.table continuation) (by omega) hc
  simpa [table,show 14+(16+states)=30+states by omega] using hl

def cost (zeros width : Nat) : Nat :=
  (zeros+1)*(8*width+11)+(8*width+13)

/-- `zeros+1` is the actual number of leading zero cells. This positive
condition is needed by the compactor's stop-on-sentinel interface. -/
theorem erase_then (continuation : Nat → Bool → Row) (zeros : Nat) (w : List Bool)
    (certificate tail fuel : Nat) :
    run (table continuation) ⟨2^(zeros+1)*(2*certificate+1),2*flipped w tail,some 0⟩
      (cost zeros w.length+fuel) =
    shiftConfig 30 (run continuation
      ⟨certificate,2*flipped w (2^(zeros+2)*tail),some 0⟩ fuel) := by
  have ht : cost zeros w.length+fuel =
      (zeros+1)*(8*w.length+11)+(8*w.length+13+fuel) := by simp [cost]; omega
  rw [ht]
  unfold table
  rw [Source284ScratchCompactLoop.countdown_after,Source284ClearOddBoundary.clear_then,
    Source284SourceRelocation.shiftConfig_add]
  congr 2
  rw [pow_succ]
  ring

namespace Fixtures
def loop (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩
example : run (table loop) ⟨14,0,some 0⟩ 24 = ⟨3,0,some 30⟩ := by decide +kernel
example : run (table loop) ⟨28,150,some 0⟩ 83 = ⟨3,1046,some 30⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284EraseZeroBlock
