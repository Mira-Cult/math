import Shared.Beeping.NPcoNP.Source284PayloadReset
import Shared.Beeping.NPcoNP.Source284UnaryClear

/-! Finite sequential reset of unary token marks and payload marks. The
tape must have the comparator's marked-prefix form; the certificate and
high suffix are preserved and a caller continuation is reached. -/
namespace Shared.Beeping.NPcoNP.Source284MatchReset

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284UnaryClear.table (Source284PayloadReset.table continuation)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (18+states) (table continuation) := by
  have hp := Source284PayloadReset.closed states continuation hn hv
  have hu := Source284UnaryClear.closed (11+states) (Source284PayloadReset.table continuation) (by omega) hp
  have he : 7+(11+states) = 18+states := by omega
  rw [he] at hu
  exact hu

/-- The whole token sequence is cleared; on the payload side precisely the
zero-marked prefix is restored. Both phases and their return movements are
charged. -/
theorem reset (continuation : Nat → Bool → Row) (tokens xs rest : List Bool)
    (certificate tail : Nat) :
    run (table continuation)
      ⟨pairTape tokens certificate,2*zeros xs (flipped (rest++[false]) tail),some 0⟩
      ((4*tokens.length+6)+(4*(xs.length+rest.length)+12)) =
    ⟨pairTape (List.replicate tokens.length false) certificate,
      2*flipped ((xs++rest)++[false]) tail,some 18⟩ := by
  unfold table
  rw [run_add,Source284UnaryClear.clear]
  change run (Source284UnaryClear.table (Source284PayloadReset.table continuation))
    (shiftConfig 7 ⟨pairTape (List.replicate tokens.length false) certificate,
      2*zeros xs (flipped (rest++[false]) tail),some 0⟩) _ = _
  rw [Source284UnaryClear.relocated_run,Source284PayloadReset.reset_sentinel]
  rfl

/-- Both reset phases have positive cost, even for empty token and payload
sequences. -/
theorem cost_positive (tokens xs rest : List Bool) :
    0 < (4*tokens.length+6)+(4*(xs.length+rest.length)+12) := by omega

end Shared.Beeping.NPcoNP.Source284MatchReset
