import Shared.Beeping.NPcoNP.Source284HardwireGuarded
import Shared.Beeping.NPcoNP.Source284TableClockBound

/-! An explicit sufficient unary reference clock for a hardwired finite
table with a per-instance countdown guard. The number of logical states and
the chosen extra clock have elementary polynomial bounds. These are size and
extensional facts only: an effective uniform serializer and its running time
are not supplied here. -/

namespace Shared.Beeping.NPcoNP.Source284HardwireClock

open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable
open Shared.Beeping.NPcoNP.Source284HardwireGuarded
open Shared.Beeping.NPcoNP.Source284TableFrame
open Shared.Beeping.NPcoNP.Source284TableClock
open Shared.Beeping.NPcoNP.Source284TableClockBound
open Shared.Beeping.NPcoNP.Source284HardnessFramePoly
open Shared.Beeping.NPcoNP.Source284Comparison

def states (bits : List Bool) (n cutoff : Nat) : Nat :=
  offset bits + Source284TableCountdown.allocated n cutoff

def guardedTable (bits : List Bool) (original : Nat → Bool → Row)
    (n cutoff : Nat) : Nat → Bool → Row :=
  table bits (Source284TableCountdown.table n cutoff original)

/-- A deliberately generous code-length allowance, paid in unary. -/
def extra (bits : List Bool) (n cutoff : Nat) : Nat :=
  codeBound (states bits n cutoff) + 1

def outerClock (bits : List Bool) (n cutoff : Nat) : Nat :=
  offset bits + (cutoff + extra bits n cutoff)

def framedInput (bits : List Bool) (original : Nat → Bool → Row)
    (n cutoff : Nat) : List Bool :=
  let code := programBits (states bits n cutoff) (guardedTable bits original n cutoff)
  produceSafe (code, padFor code (outerClock bits n cutoff))

theorem guarded_closed (bits : List Bool) (original : Nat → Bool → Row)
    (n cutoff : Nat) : Closed (states bits n cutoff) (guardedTable bits original n cutoff) := by
  apply Source284HardwireTable.closed bits (Source284TableCountdown.table n cutoff original)
  · simp [Source284TableCountdown.allocated]
  · exact Source284TableCountdown.closed n cutoff original

theorem code_fits (bits : List Bool) (original : Nat → Bool → Row)
    (n cutoff : Nat) :
    (programBits (states bits n cutoff) (guardedTable bits original n cutoff)).length + 1 ≤
      outerClock bits n cutoff := by
  have hb := programBits_length_le (states bits n cutoff)
    (guardedTable bits original n cutoff) (guarded_closed bits original n cutoff)
  dsimp [outerClock, extra]
  omega

/-- The selected clock is always sufficient, and the reference's result is
the original cutoff-T answer over certificates below `2^T`. -/
theorem reference_exact (bits : List Bool) (original : Nat → Bool → Row)
    (n cutoff : Nat) (hn : 0 < n) (hclosed : Closed n original) :
    reference (value (framedInput bits original n cutoff)) = true ↔
      ∃ certificate, certificate < 2^cutoff ∧
        (run original ⟨certificate,value bits,some 0⟩ cutoff).state.isNone = true := by
  have h := reference_guarded_original_bound bits original n cutoff hn hclosed
    (extra bits n cutoff) (code_fits bits original n cutoff)
  simpa [framedInput, states, guardedTable, outerClock] using h

/-- A polynomial upper bound on the allocated logical state count. -/
def stateCap (bits : List Bool) (n cutoff : Nat) : Nat :=
  2*bits.length + 3 + (n+cutoff+1)^2

theorem states_le (bits : List Bool) (n cutoff : Nat) :
    states bits n cutoff ≤ stateCap bits n cutoff := by
  have ha := Source284TableCountdown.allocated_le n cutoff
  have hm : max n cutoff + 1 ≤ n+cutoff+1 := by omega
  have hs := Nat.pow_le_pow_left hm 2
  dsimp [states, stateCap, offset]
  omega

/-- The extra unary clock has this explicit polynomial bound in input length,
table state count, and the original unary cutoff. This is not a compiler
running-time bound. -/
theorem extra_le (bits : List Bool) (n cutoff : Nat) :
    extra bits n cutoff ≤
      2 + 2*stateCap bits n cutoff*(8*stateCap bits n cutoff+8) := by
  have hs := states_le bits n cutoff
  have ht : 8*states bits n cutoff+8 ≤ 8*stateCap bits n cutoff+8 := by omega
  have hp := Nat.mul_le_mul hs ht
  dsimp [extra, codeBound]
  nlinarith

end Shared.Beeping.NPcoNP.Source284HardwireClock
