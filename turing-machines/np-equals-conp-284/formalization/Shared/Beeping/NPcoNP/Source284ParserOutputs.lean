import Shared.Beeping.NPcoNP.Source284Suffix
import Shared.ComplexityBridge.TM2ListReverse
import Shared.ComplexityBridge.TM2GateCNFPieces
import Shared.ComplexityBridge.TM2Constant

/-! Output conversion for the 284 source framing parser. A payload list is
used directly as a unary clock, while its reversal followed by the sentinel
is the program description in the shared low-endian representation. This
does not assert that the payload parser itself runs in polynomial time. -/

namespace Shared.Beeping.NPcoNP.Source284ParserOutputs

open Shared.ComplexityBridge
open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284Parser

/-- First component is a unary clock; its bit values do not matter. -/
def outputs (payload : List Bool) : List Bool × List Bool :=
  (payload, payload.reverse ++ [true])

theorem clock_length (payload : List Bool) : (outputs payload).1.length = payload.length := rfl

/-- Reversing the payload and appending the high sentinel implements the
source's repeated `2*e + bit` update, starting from one. -/
theorem description_value (payload : List Bool) :
    value (outputs payload).2 = payloadFold 1 payload := by
  rw [outputs, bitValue_append, payloadFold_value]
  simp [value, Nat.add_comm]

theorem outputs_isPolyTime : ComplexityTheory.IsPolyTime outputs := by
  let rev : List Bool → List Bool := List.reverse
  let marker : List Bool → List Bool := fun _ => [true]
  have hr : ComplexityTheory.IsPolyTime rev := TM2ListReverse.reverse_isPolyTime
  have hm : ComplexityTheory.IsPolyTime marker := by
    have ht : ComplexityTheory.IsPolyTime (fun _ : List Bool => true) := TM2Constant.isPolyTime true
    simpa [marker] using TM2GateCNFPieces.singleton_isPolyTime (fun _ : List Bool => true) ht
  have hp := TM2GuardAllStep.pair_isPolyTime rev marker hr hm
  have ha := TM2Compose.isPolyTime_comp (fun xs : List Bool => (rev xs,marker xs))
    (TM2ListAppend.append (α := Bool)) hp TM2ListAppend.append_isPolyTime
  have hid : ComplexityTheory.IsPolyTime (id : List Bool → List Bool) :=
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hresult := TM2GuardAllStep.pair_isPolyTime id
    (fun xs : List Bool => xs.reverse ++ [true]) hid (by simpa [rev, marker, TM2ListAppend.append] using ha)
  change ComplexityTheory.IsPolyTime (fun xs : List Bool => (xs, xs.reverse ++ [true]))
  exact hresult

end Shared.Beeping.NPcoNP.Source284ParserOutputs
