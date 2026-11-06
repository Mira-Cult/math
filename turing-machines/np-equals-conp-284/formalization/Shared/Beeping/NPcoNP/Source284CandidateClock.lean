import Shared.Beeping.NPcoNP.Source284ParserTM2
import Shared.Beeping.NPcoNP.Source284Comparison
import Shared.ComplexityBridge.TM2UnaryPolynomialIO

/-! The selected candidate clock, generated in unary by the canonical TM2
model. The exponent is fixed for each machine; it is not part of the input.
This is a clock construction, not yet a candidate-verifier or class theorem. -/

namespace Shared.Beeping.NPcoNP.Source284CandidateClock

open Shared.Beeping.NPcoNP.Source284ParserTM2
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.ComplexityBridge
open Shared.Codes.BitNumeralCompare (value)

/-- Generate the source candidate clock from the actual parsed prefix. -/
def clock (j : Nat) (xs : List Bool) : List Bool :=
  List.replicate (((parse xs).1.length + 1) ^ j) true

theorem clock_isPolyTime (j : Nat) : ComplexityTheory.IsPolyTime (clock j) := by
  have hp : ComplexityTheory.IsPolyTime (fun xs : List Bool => (parse xs).1) :=
    TM2Compose.isPolyTime_comp parse (fun p : List Bool × List Bool => p.1)
      parse_isPolyTime TM2PairFirst.first_isPolyTime
  let p : Polynomial Nat := (Polynomial.X + Polynomial.C 1) ^ j
  have h := TM2Compose.isPolyTime_comp (fun xs : List Bool => (parse xs).1)
    (TM2UnaryPolynomialIO.unaryPolynomial p) hp
    (TM2UnaryPolynomialIO.unaryPolynomial_isPolyTime p)
  have he : (fun xs : List Bool => TM2UnaryPolynomialIO.unaryPolynomial p (parse xs).1) = clock j := by
    funext xs
    simp [clock, TM2UnaryPolynomialIO.unaryPolynomial, p]
  simpa only [he] using h

/-- This includes the empty-prefix boundary, where the clock is one. -/
theorem clock_length (j : Nat) (xs : List Bool) :
    (clock j xs).length = Source284Comparison.clock j (value xs) := by
  simp [clock, Source284Comparison.clock, Source284ParserTM2.clock_length]

end Shared.Beeping.NPcoNP.Source284CandidateClock
