import Shared.Beeping.NPcoNP.Source284RectangularPolynomial

/-! One paid multiplication stage on a supplied power-sized token block.
This does not generate that block or recycle the resulting counter. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284PreparedPowerStage

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)
open Shared.Beeping.NPcoNP.Source284SquareRepeat (repeatTable)
open Shared.Beeping.NPcoNP.Source284RectangularRepeat (repeatCost)

/-- From prepared blocks of lengths `n` and `n^e`, the actual finite table
produces an `n^(e+1)` counter, retaining the input blocks and certificate. -/
theorem power_stage (e n : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate higher fuel : Nat) :
    run (repeatTable 1 continuation)
      ⟨pairTape (List.replicate (n^e) false) (pairTape (List.replicate n false) certificate),
        2*flipped w (counter 0 higher),some 0⟩
      (repeatCost 1 n (n^e) 0 w.length+fuel) =
    shiftConfig 110 (run continuation
      ⟨pairTape (List.replicate (n^e) false) (pairTape (List.replicate n false) certificate),
        2*flipped w (counter (n^(e+1)) (halves (n^(e+1)) higher)),some 0⟩ fuel) := by
  have h := Source284RectangularRepeat.repeat_then 1 continuation n (n^e) 0 w certificate higher fuel
  simpa [Nat.pow_succ,Nat.mul_comm] using h

/-- For each fixed exponent the transition count is bounded by one explicit
polynomial in `n` when the retained payload width is at most `n+1`. -/
theorem powerCost_polynomial (e n width : Nat) (hwidth : width ≤ n+1) :
    repeatCost 1 n (n^e) 0 width ≤
      (Source284RectangularPolynomial.costPolynomial 1 Polynomial.X (Polynomial.X^e)
        0 (Polynomial.X+1)).eval n := by
  apply Source284RectangularPolynomial.repeatCost_polynomial
  · simp
  · simp
  · simp
  · simpa using hwidth

end Shared.Beeping.NPcoNP.Source284PreparedPowerStage
