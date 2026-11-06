import Shared.Beeping.NPcoNP.Source284HardnessFramePoly
import Shared.Beeping.NPcoNP.Source284SentinelAcceptance

/-! A constructive unary-clock reduction to the 284 source reference. The
input is a pair of raw low-endian source-program bits and unary padding; its
bounded acceptance starts with zero input and the certificate on the left.
The source clock is exactly code length plus padding length plus one. This is
not a SAT reduction, an NP-hardness proof, or a physical-machine refinement. -/

namespace Shared.Beeping.NPcoNP.Source284UnaryFrameReduction

open Shared.Beeping.NPcoNP.Source284HardnessFrame
open Shared.Beeping.NPcoNP.Source284HardnessFramePoly
open Shared.Beeping.NPcoNP.Source284SentinelAcceptance
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Codes.BitNumeralCompare

abbrev Input := List Bool × List Bool

def time (p : Input) : Nat := p.1.length + (p.2.length + 1)

/-- The bounded-source language has no hidden answers: all certificates
below the clock's binary capacity are checked by the executable evaluator. -/
def boundedSource (p : Input) : Bool :=
  acceptBound (value p.1) 0 (time p) (2 ^ time p)

/-- The separator-protected frame is an actual uniform polynomial-time
function on the canonical encoding of the full program/unary-padding pair. -/
theorem reduction_isPolyTime : ComplexityTheory.IsPolyTime produceSafe :=
  produceSafe_isPolyTime

/-- The source reference on the framed input equals the original source
program's bounded acceptance at exactly the specified clock. -/
theorem reduction_correct (p : Input) :
    reference (value (produceSafe p)) = boundedSource p := by
  rw [produceSafe_eq_input, reference_input]
  unfold boundedSource time description Source284HardnessFrame.clock
  exact sentinel_acceptBound p.1 p.2.length 0 _ _

/-- Soundness and completeness for each finite certificate search, including
zero-length program descriptions and arbitrary unary padding bit values. -/
theorem reduction_correct_iff (p : Input) :
    reference (value (produceSafe p)) = true ↔
      ∃ certificate, certificate < 2 ^ time p ∧
        accepts (value p.1) 0 certificate (time p) = true := by
  rw [reduction_correct, boundedSource, acceptBound_iff]

/-- The entire canonical output encoding is linearly bounded by the full
encoded input pair, including its unary padding. -/
theorem reduction_encoded_linear (p : Input) :
    (BitstringEncoding.bitEncode (produceSafe p)).length ≤
      2 * (BitstringEncoding.bitEncode p).length + 7 :=
  produceSafe_encoded_linear p

end Shared.Beeping.NPcoNP.Source284UnaryFrameReduction
