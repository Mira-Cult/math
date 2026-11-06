import Shared.Beeping.NPcoNP.Source284HardwireCorrect
import Shared.Beeping.NPcoNP.Source284TableClock

/-! Exact reference framing for a source-relative table with a hardwired
input. The reference searches certificates up to `2^(loader overhead + T)`;
this is not the original T-bit witness bound. The code-size premise is
explicit, as are the extra loader transitions. No timeout guard, effective
uniform compiler, or complexity-class hardness result is asserted. -/

namespace Shared.Beeping.NPcoNP.Source284HardwireReference

open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable
open Shared.Beeping.NPcoNP.Source284HardwireCorrect
open Shared.Beeping.NPcoNP.Source284TableFrame
open Shared.Beeping.NPcoNP.Source284TableClock
open Shared.Beeping.NPcoNP.Source284HardnessFramePoly
open Shared.Beeping.NPcoNP.Source284Comparison

theorem loader_isNone (bits : List Bool) (original : Nat → Bool → Row)
    (certificate clock : Nat) :
    (run (table bits original) ⟨certificate,0,some 0⟩ (offset bits+clock)).state.isNone =
      (run original ⟨certificate,value bits,some 0⟩ clock).state.isNone := by
  rw [loader_then_run]
  change ((run original ⟨certificate,value bits,some 0⟩ clock).state.map
    (fun q => offset bits + q)).isNone = _
  cases h : (run original ⟨certificate,value bits,some 0⟩ clock).state <;> simp [h]

/-- The source reference tests the original table on the fixed input after
paying the entire loader, at precisely the requested original clock. The
reference's actual larger certificate range remains visible in the result. -/
theorem reference_hardwired_table (bits : List Bool) (original : Nat → Bool → Row)
    (n : Nat) (hn : 0 < n) (hclosed : Closed n original) (clock : Nat)
    (hclock : (programBits (offset bits+n) (table bits original)).length + 1 ≤
      offset bits+clock) :
    reference (value (produceSafe (programBits (offset bits+n) (table bits original),
      padFor (programBits (offset bits+n) (table bits original)) (offset bits+clock)))) = true ↔
      ∃ certificate, certificate < 2 ^ (offset bits+clock) ∧
        (run original ⟨certificate,value bits,some 0⟩ clock).state.isNone = true := by
  have hpositive : 0 < offset bits+n := by dsimp [offset]; omega
  rw [reference_at_clock (offset bits+n) (table bits original) hpositive
    (closed bits original n hn hclosed) (offset bits+clock) hclock]
  simp only [loader_isNone]

end Shared.Beeping.NPcoNP.Source284HardwireReference
