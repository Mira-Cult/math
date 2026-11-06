import Shared.Beeping.NPcoNP.Source284TableClock
import Shared.Beeping.NPcoNP.Source284TableSize

/-! A uniform sufficient clock for a closed finite relative table. The bound
is on the bit length of its finite record code, not on the time to construct
that code or to simulate any other machine model. -/

namespace Shared.Beeping.NPcoNP.Source284TableClockBound

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284TableFrame
open Shared.Beeping.NPcoNP.Source284TableClock
open Shared.Beeping.NPcoNP.Source284TableSize
open Shared.Beeping.NPcoNP.Source284HardnessFramePoly
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Codes.BitNumeralCompare

def codeBound (n : Nat) : Nat := 1 + 2*n*(8*n+8)

/-- Closed tables have a source record code of quadratic bit length. -/
theorem programBits_length_le (n : Nat) (table : Nat → Bool → Row)
    (closed : Closed n table) : (programBits n table).length ≤ codeBound n := by
  simpa [programBits, codeBound, Nat.size_eq_bits_len] using
    encode_zero_size_bound n table closed

/-- A clock exceeding the explicit quadratic code bound supplies enough
unary room for the entire serialized table and the separator. -/
theorem reference_at_quadratic_clock (n : Nat) (table : Nat → Bool → Row)
    (hn : 0 < n) (closed : Closed n table) (clock : Nat)
    (hclock : codeBound n + 1 ≤ clock) :
    reference (value (produceSafe (programBits n table,
      padFor (programBits n table) clock))) = true ↔
      ∃ certificate, certificate < 2 ^ clock ∧
        (run table ⟨certificate, 0, some 0⟩ clock).state.isNone = true := by
  apply reference_at_clock n table hn closed clock
  have hs := programBits_length_le n table closed
  omega

end Shared.Beeping.NPcoNP.Source284TableClockBound
