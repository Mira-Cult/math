import Shared.Beeping.NPcoNP.Source284TableRun

/-! A concrete finite relative-table scanner for the marker/payload witness
frame.  The initial turn moves onto the certificate half while preserving
the scanned input bit. The following states scan marker/payload pairs and
stop at a control boundary immediately after a zero marker.

The boundary state is continuing, not a halt or an absorbing configuration.
This four-*logical*-state table encodes into the 284 source's numeric
description; it is not a four-state binary-tape machine. This module does
not enforce a witness cutoff, extract a list, prove a running-time bound in
the canonical complexity model, or establish candidate coverage. -/

namespace Shared.Beeping.NPcoNP.Source284WitnessScanner

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284Relative

/-- `0`: turn onto the certificate; `1`: marker; `2`: payload;
`3`: continuing boundary after the zero marker. -/
def table : Nat → Bool → Row
  | 0, b => ⟨b, true, some 1⟩
  | 1, b => ⟨b, false, some (if b then 2 else 3)⟩
  | 2, b => ⟨b, false, some 1⟩
  | _, b => ⟨b, false, some 3⟩

/-- Every represented row stays in the four-state finite table. -/
theorem table_closed : Closed 4 table := by
  intro q hq b q' hnext
  interval_cases q <;> cases b <;> simp_all [table] <;> omega

/-- Reading and writing the low bit before turning preserves the whole
original input half, including its empty or zero representation. -/
theorem lowbit_value (n : Nat) : bit (n.testBit 0) = n % 2 := by
  rw [Nat.testBit_zero]
  have h := Nat.mod_lt n (by decide : 0 < 2)
  by_cases hn : n % 2 = 1
  · simp [bit, hn]
  · have hz : n % 2 = 0 := by omega
    simp [bit, hz]

theorem bit_decide_mod (n : Nat) : bit (decide (n % 2 = 1)) = n % 2 := by
  simpa only [Nat.testBit_zero] using lowbit_value n

theorem initial_turn (certificate input : Nat) :
    Source284TableRun.step table ⟨certificate, input, some 0⟩ =
      ⟨input, certificate, some 1⟩ := by
  simp only [Source284TableRun.step, table, ↓reduceIte]
  rw [lowbit_value]
  congr 1 <;> omega

/-- A marker bit advances onto its payload or onto the zero-marker
continuation; the scanned bit is written back unchanged. -/
theorem marker_step (left right : Nat) :
    Source284TableRun.step table ⟨left, right, some 1⟩ =
      ⟨2*left + right % 2, right/2,
        some (if right.testBit 0 then 2 else 3)⟩ := by
  simp [Source284TableRun.step, table, Nat.testBit_zero, bit_decide_mod]

/-- A payload bit is written back unchanged and scanning returns to the
marker state. -/
theorem payload_step (left right : Nat) :
    Source284TableRun.step table ⟨left, right, some 2⟩ =
      ⟨2*left + right % 2, right/2, some 1⟩ := by
  simp [Source284TableRun.step, table, Nat.testBit_zero, bit_decide_mod]

/-- State `3` is a continuing control boundary, not an absorbing tape
configuration. -/
theorem continuation_step (left right : Nat) :
    Source284TableRun.step table ⟨left, right, some 3⟩ =
      ⟨2*left + right % 2, right/2, some 3⟩ := by
  simp [Source284TableRun.step, table, Nat.testBit_zero, bit_decide_mod]

/-- The finite rows in source lookup order, including both read symbols for
each of the four logical states. -/
theorem row_codes : records 4 table = [14, 15, 28, 21, 12, 13, 28, 29] := by
  decide

theorem record_count : (records 4 table).length = 8 := by simp [row_codes]

/-- Numeric source states are `1, 3, 5, 7` for the logical states; this is
not a statement about the number of physical binary-tape states. -/
theorem numeric_states :
    (List.range 4).map active = [1, 3, 5, 7] := by decide

/-- The finite source description with the virtual-zero high tail. -/
def description : Nat := encode 4 table 0

set_option maxRecDepth 8192

/-- The eight unary records occupy 168 bit positions including the final
zero terminator; its zero-tail natural description has 167 significant
binary bits. -/
theorem description_bits : Nat.size description = 167 := by decide

/-- The source evaluator executes every finite scanner run exactly, with
an arbitrary unused high tail on the encoded table description. -/
theorem source_run (tail certificate input steps : Nat) :
    Source284Relative.run (encode 4 table tail)
      (Source284Relative.initial input certificate) steps =
      toSource (Source284TableRun.run table ⟨certificate, input, some 0⟩ steps) := by
  have hv : Valid 4 ⟨certificate, input, some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    omega
  simpa [Source284Relative.initial, toSource, nextState, active] using
    run_toSource 4 table tail ⟨certificate, input, some 0⟩ table_closed hv steps

end Shared.Beeping.NPcoNP.Source284WitnessScanner
