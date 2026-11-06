import Shared.Beeping.NPcoNP.Source284RecordBitCost
import Shared.ComplexityBridge.TM2ContextMapGeneric
import Shared.ComplexityBridge.TM2GateDispatch

/-! Canonical polynomial-time implementation of the binary-index zero test
used by the source record scanner. The input is an arbitrary bit list, so
redundant high zeroes are preserved in scope. -/
namespace Shared.Beeping.NPcoNP.Source284ZeroTM2

open Shared.Beeping.NPcoNP.Source284RecordBitCost

theorem zero_as_all (xs : List Bool) :
    isZero xs = (xs.map (fun b => !b)).all id := by
  induction xs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [isZero, ih]

/-- The implemented list map and Boolean-list test are both canonical TM2
polynomial-time functions; composition charges the intermediate list. -/
theorem isZero_isPolyTime : ComplexityTheory.IsPolyTime isZero := by
  let negate : List Bool → List Bool := fun xs => xs.map (fun b => !b)
  have hm : ComplexityTheory.IsPolyTime negate :=
    Shared.ComplexityBridge.TM2ContextMapGeneric.listMap_isPolyTime
      (fun b : Bool => !b) Shared.ComplexityBridge.TM2GateDispatch.not_isPolyTime
  have h := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp negate
    (fun xs : List Bool => xs.all id) hm Shared.ComplexityBridge.TM2GateDispatch.all_isPolyTime
  have he : (fun xs : List Bool => (negate xs).all id) = isZero := by
    funext xs
    exact (zero_as_all xs).symm
  rw [he] at h
  exact h

end Shared.Beeping.NPcoNP.Source284ZeroTM2
