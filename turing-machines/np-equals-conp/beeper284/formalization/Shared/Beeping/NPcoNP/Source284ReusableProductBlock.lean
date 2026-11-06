import Shared.Beeping.NPcoNP.Source284CounterTokenRecycle

/-! Two paid rectangular passes followed by the counter-to-token adapter
create a reusable product-sized token block. Existing blocks, payload and
certificate remain explicitly represented; raw initialization and further
block scheduling are separate obligations. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284ReusableProductBlock

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)
open Shared.Beeping.NPcoNP.Source284RectangularRepeat (repeatCost)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284SquareRepeat.repeatTable 2 (Source284CounterTokenRecycle.table continuation)

def cost (outer inner width : Nat) : Nat :=
  repeatCost 2 outer inner 1 width+Source284CounterTokenRecycle.cost (outer*inner) width

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (255+states) (table continuation) := by
  have hr := Source284CounterTokenRecycle.closed states continuation hn hv
  have hs := Source284SquareRepeat.repeat_closed 2 (35+states)
    (Source284CounterTokenRecycle.table continuation) (by omega) hr
  have he : 110*2+(35+states)=255+states := by omega
  rw [he] at hs
  exact hs

/-- The finite table constructs a new product block in front of both old
blocks. Its one-bit counter seed, all high suffix effects and all transitions
are explicit. -/
theorem product_then (outer inner : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate higher fuel : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate inner false) (pairTape (List.replicate outer false) certificate),
        2*flipped w (counter 1 higher),some 0⟩ (cost outer inner w.length+fuel) =
    shiftConfig 255 (run continuation
      ⟨pairTape (List.replicate (outer*inner) false)
          (pairTape (List.replicate inner false) (pairTape (List.replicate outer false) certificate)),
        2*flipped w (halves (2*(outer*inner)) higher),some 0⟩ fuel) := by
  have ht : cost outer inner w.length+fuel = repeatCost 2 outer inner 1 w.length+
      (Source284CounterTokenRecycle.cost (outer*inner) w.length+fuel) := by simp [cost]; omega
  rw [ht]
  change run (Source284SquareRepeat.repeatTable 2 (Source284CounterTokenRecycle.table continuation)) _ _ = _
  rw [Source284RectangularRepeat.repeat_then]
  have hn : 1+2*(outer*inner) = 2*(outer*inner)+1 := by omega
  rw [hn,Source284CounterTokenRecycle.recycle_then,Source284SourceRelocation.shiftConfig_add]

/-- The same operational result holds for the actual encoded source table,
from the explicitly prepared configuration. -/
theorem encoded_product_then (outer inner states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate higher fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (encode (255+states) (table continuation) 1)
      ⟨pairTape (List.replicate inner false) (pairTape (List.replicate outer false) certificate),
        2*flipped w (counter 1 higher),active 0⟩ (cost outer inner w.length+fuel) =
    toSource (shiftConfig 255 (run continuation
      ⟨pairTape (List.replicate (outer*inner) false)
          (pairTape (List.replicate inner false) (pairTape (List.replicate outer false) certificate)),
        2*flipped w (halves (2*(outer*inner)) higher),some 0⟩ fuel)) := by
  let c : Config := ⟨pairTape (List.replicate inner false) (pairTape (List.replicate outer false) certificate),
    2*flipped w (counter 1 higher),some 0⟩
  have hc : Valid (255+states) c := by intro q hq; simp [c] at hq; omega
  have h := run_toSource (255+states) (table continuation) 1 c (closed states continuation hn hv) hc
    (cost outer inner w.length+fuel)
  rw [product_then] at h
  exact h

end Shared.Beeping.NPcoNP.Source284ReusableProductBlock
