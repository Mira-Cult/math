import Shared.Beeping.NPcoNP.Source284TableFrame

/-! A sufficient unary clock for the 284 reference frame. The source clock
must include the table code and a separating bit. These are exact finite
semantics, not a polynomial-time compiler for function-valued tables. -/

namespace Shared.Beeping.NPcoNP.Source284TableClock

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284TableFrame
open Shared.Beeping.NPcoNP.Source284UnaryFrameReduction
open Shared.Beeping.NPcoNP.Source284HardnessFramePoly
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Codes.BitNumeralCompare

/-- Unary padding needed for a requested clock, after the mandatory code
and separator. A too-small request is handled by truncated subtraction. -/
def padFor (code : List Bool) (clock : Nat) : List Bool :=
  List.replicate (clock - code.length - 1) false

theorem time_padFor (code : List Bool) (clock : Nat)
    (h : code.length + 1 ≤ clock) : time (code, padFor code clock) = clock := by
  simp [time, padFor]
  omega

/-- The actual reference decides the closed finite table's bounded
existential acceptance at every requested clock large enough for its code. -/
theorem reference_at_clock (n : Nat) (table : Nat → Bool → Row)
    (hn : 0 < n) (closed : Closed n table) (clock : Nat)
    (hclock : (programBits n table).length + 1 ≤ clock) :
    reference (value (produceSafe (programBits n table,
      padFor (programBits n table) clock))) = true ↔
      ∃ certificate, certificate < 2 ^ clock ∧
        (run table ⟨certificate, 0, some 0⟩ clock).state.isNone = true := by
  have h := reference_iff_table n table hn closed (padFor (programBits n table) clock)
  rw [time_padFor _ _ hclock] at h
  exact h

/-- Under the same hypothesis the raw framed reference input contains
exactly two bits per unit of clock, plus its final zero marker. -/
theorem framed_length (code : List Bool) (clock : Nat)
    (h : code.length + 1 ≤ clock) :
    (produceSafe (code, padFor code clock)).length = 2 * clock + 1 := by
  rw [produceSafe_eq_input, Shared.Beeping.NPcoNP.Source284HardnessFrame.input_length]
  simp [Shared.Beeping.NPcoNP.Source284HardnessFrame.clock, padFor]
  omega

end Shared.Beeping.NPcoNP.Source284TableClock
