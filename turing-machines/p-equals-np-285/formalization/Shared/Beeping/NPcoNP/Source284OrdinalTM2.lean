import Shared.Beeping.NPcoNP.Source284EvaluatorBitStep
import Shared.Beeping.NPcoNP.Source284IncrementTM2
import Shared.Beeping.NPcoNP.Source284DecrementTM2
import Shared.ComplexityBridge.TM2If

/-! Canonical polynomial-time implementation of the binary row ordinal
used by the 284 source evaluator. This is a single helper, not yet the
whole evaluator step or its iteration. -/
namespace Shared.Beeping.NPcoNP.Source284OrdinalTM2

open Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284RecordBitCost
open Shared.Beeping.NPcoNP.Source284UnaryCountBits
open Shared.Beeping.NPcoNP.Source284EvaluatorBitStep

abbrev Input := List Bool × Bool

/-- The source first decrements the state bits, then increments them only
when the scanned tape bit is one. Both branches are charged by TM2If. -/
theorem ordinal_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : Input => ordinal p.1 p.2) := by
  let state : Input → List Bool := fun p => p.1
  let read : Input → Bool := fun p => p.2
  let before : Input → List Bool := fun p => decBits (state p)
  let after : Input → List Bool := fun p => incrementData (before p)
  have hs : ComplexityTheory.IsPolyTime state := TM2PairFirst.first_isPolyTime
  have hr : ComplexityTheory.IsPolyTime read := TM2GuardAllStep.second_isPolyTime
  have hb : ComplexityTheory.IsPolyTime before :=
    TM2Compose.isPolyTime_comp state decBits hs Source284DecrementTM2.decBits_isPolyTime
  have ha : ComplexityTheory.IsPolyTime after :=
    TM2Compose.isPolyTime_comp before incrementData hb Source284IncrementTM2.incrementData_isPolyTime
  have h := TM2If.if_isPolyTime read after before hr ha hb
  change ComplexityTheory.IsPolyTime (fun p : Input => ordinal p.1 p.2)
  exact h

end Shared.Beeping.NPcoNP.Source284OrdinalTM2
