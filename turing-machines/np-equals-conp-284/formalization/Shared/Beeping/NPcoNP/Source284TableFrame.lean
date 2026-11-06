import Shared.Beeping.NPcoNP.Source284UnaryFrameReduction
import Shared.Beeping.NPcoNP.Source284TableRun
import Shared.Codes.BinaryAdditionCanonical

/-! Exact composition of the finite relative-table compiler and the 284
source reference's unary-padding frame. A table is still an arbitrary Lean
function, so these theorems are extensional: they do not give an effective
serialization of table inputs, a polynomial-time reduction from a finite
table language, or a complexity-class hardness result. -/

namespace Shared.Beeping.NPcoNP.Source284TableFrame

open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284UnaryFrameReduction
open Shared.Beeping.NPcoNP.Source284HardnessFramePoly
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Codes.BitNumeralCompare

/-- Canonical low-endian bits of the finite record code. The zero tail is
safe because every reachable table state has its rows in the prefix. -/
def programBits (n : Nat) (table : Nat → Bool → Row) : List Bool :=
  (encode n table 0).bits

theorem programBits_value (n : Nat) (table : Nat → Bool → Row) :
    value (programBits n table) = encode n table 0 :=
  Shared.Codes.BinaryAdditionCanonical.value_bits _

/-- For the actual source reference input produced from a finite table code
and unary padding, the reference bit is the finite table's existential
acceptance on zero input at exactly the frame-supplied clock. -/
theorem reference_iff_table (n : Nat) (table : Nat → Bool → Row)
    (hn : 0 < n) (closed : Closed n table) (padding : List Bool) :
    reference (value (produceSafe (programBits n table, padding))) = true ↔
      ∃ certificate, certificate < 2 ^ time (programBits n table, padding) ∧
        (run table ⟨certificate, 0, some 0⟩
          (time (programBits n table, padding))).state.isNone = true := by
  rw [reduction_correct_iff]
  simp only [programBits_value]
  simp only [bounded_acceptance n table 0 hn closed]

end Shared.Beeping.NPcoNP.Source284TableFrame
