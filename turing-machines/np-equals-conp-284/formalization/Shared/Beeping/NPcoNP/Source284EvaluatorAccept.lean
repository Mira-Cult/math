import Shared.Beeping.NPcoNP.Source284EvaluatorUnary

/-! Boolean acceptance projection for the canonically polynomial-time unary
bounded evaluator. Inputs contain an explicit initial state and unary clock;
this module does not implement the source parser or its witness guard. -/

namespace Shared.Beeping.NPcoNP.Source284EvaluatorAccept

open Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EvaluatorBitStep
open Shared.Beeping.NPcoNP.Source284EvaluatorPackedStep
open Shared.Beeping.NPcoNP.Source284EvaluatorUnary
open Shared.Beeping.NPcoNP.Source284RecordBitCost
open Shared.Codes.BitNumeralCompare (value)

def accepts (p : Packed × List Bool) : Bool := isZero (state (evaluate p))

/-- The state-zero output test uses an actual canonical TM2 machine and is
composed with the audited bounded evaluator. -/
theorem accepts_isPolyTime : ComplexityTheory.IsPolyTime accepts := by
  have hs : ComplexityTheory.IsPolyTime state := TM2GuardAllStep.second_isPolyTime
  have hstate := TM2Compose.isPolyTime_comp evaluate state evaluate_isPolyTime hs
  exact TM2Compose.isPolyTime_comp (fun p => state (evaluate p)) isZero hstate
    Source284ZeroTM2.isZero_isPolyTime

/-- The Boolean output agrees with the independent numerical evaluator's
state-zero test, for arbitrary packed data and every finite unary clock. -/
theorem accepts_correct (p : Packed) (clock : List Bool) :
    accepts (p,clock) =
      ((Source284Relative.run (value (code p)) (denote (config p)) clock.length).state == 0) := by
  have h := congrArg (fun c : Source284Relative.Config => c.state) (evaluate_correct p clock)
  change value (state (evaluate (p,clock))) = _ at h
  have hz := isZero_correct (state (evaluate (p,clock)))
  cases hl : isZero (state (evaluate (p,clock))) <;>
    cases hr : (Source284Relative.run (value (code p)) (denote (config p)) clock.length).state == 0 <;>
    simp_all [accepts, beq_iff_eq]

end Shared.Beeping.NPcoNP.Source284EvaluatorAccept
