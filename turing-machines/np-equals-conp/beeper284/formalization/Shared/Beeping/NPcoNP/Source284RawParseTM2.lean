import Shared.Beeping.NPcoNP.Source284ParseFoldCorrect
import Shared.Beeping.NPcoNP.Source284ParseFoldBounds
import Shared.ComplexityBridge.TM2FoldGenericBounds
import Shared.ComplexityBridge.TM2ListReverse
import Shared.ComplexityBridge.TM2GateCNFPieces

/-! Canonical polynomial-time computation of the 284 source's raw-list
marker/payload parser.  The input includes any redundant high zeroes; one
explicit false bit supplies a missing payload at the virtual end of input.
This module does not establish physical refinement or NP membership. -/

set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284RawParseTM2

open Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284ParseFoldStep
open Shared.Beeping.NPcoNP.Source284ParseFoldCorrect
open Shared.Beeping.NPcoNP.Source284RawParse

/-- One extra bit suffices for the source's virtual-zero convention. -/
def padded (xs : List Bool) : List Bool := xs ++ [false]

theorem padded_isPolyTime : ComplexityTheory.IsPolyTime padded := by
  have hid : ComplexityTheory.IsPolyTime (id : List Bool → List Bool) :=
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hfalse : ComplexityTheory.IsPolyTime (fun _ : List Bool => false) :=
    TM2Constant.isPolyTime false
  have hf : ComplexityTheory.IsPolyTime (fun _ : List Bool => [false]) := by
    simpa using TM2GateCNFPieces.singleton_isPolyTime (fun _ : List Bool => false) hfalse
  have hp := TM2GuardAllStep.pair_isPolyTime id (fun _ : List Bool => [false]) hid hf
  have h := TM2Compose.isPolyTime_comp (fun xs : List Bool => (xs,[false]))
    (TM2ListAppend.append (α := Bool)) hp TM2ListAppend.append_isPolyTime
  change ComplexityTheory.IsPolyTime (fun xs : List Bool => xs ++ [false])
  simpa only [TM2ListAppend.append] using h

/-- The actual canonical fold has a linear bound for every prefix state. -/
theorem fold_isPolyTime : ComplexityTheory.IsPolyTime
    (TM2FoldGenericIO.result Source284ParseFoldStep.step) := by
  apply TM2FoldGenericBounds.isPolyTime_of_prefix_bound
    Source284ParseFoldStep.step Source284ParseFoldStep.step_isPolyTime
  refine ⟨Polynomial.X, ?_⟩
  intro flags xs pref tail hxs
  simpa only [Polynomial.eval_X] using
    Source284ParseFoldBounds.prefix_encoded_bound flags xs pref tail hxs

def foldInput (xs : List Bool) : (Bool × Bool) × List Bool :=
  ((false,false),padded xs)

theorem foldInput_isPolyTime : ComplexityTheory.IsPolyTime foldInput := by
  have hf : ComplexityTheory.IsPolyTime (fun _ : List Bool => false) :=
    TM2Constant.isPolyTime false
  have hc : ComplexityTheory.IsPolyTime (fun _ : List Bool => (false,false)) :=
    TM2GuardAllStep.pair_isPolyTime (fun _ : List Bool => false) (fun _ : List Bool => false) hf hf
  exact TM2GuardAllStep.pair_isPolyTime (fun _ : List Bool => (false,false)) padded hc padded_isPolyTime

/-- The source-order payload list is computable by a concrete canonical TM2
within polynomial time. The proof composes a finite machine for each step,
the proved fold bounds and the canonical list reverse machine. -/
theorem payload_isPolyTime : ComplexityTheory.IsPolyTime payload := by
  let folded := TM2FoldGenericIO.result Source284ParseFoldStep.step
  let output : Packed → List Bool := fun p => p.2
  have ho : ComplexityTheory.IsPolyTime output := TM2GuardAllStep.second_isPolyTime
  have hf := TM2Compose.isPolyTime_comp foldInput folded foldInput_isPolyTime fold_isPolyTime
  have hp := TM2Compose.isPolyTime_comp (fun xs => folded (foldInput xs)) output hf ho
  have hr := TM2Compose.isPolyTime_comp (fun xs => output (folded (foldInput xs)))
    (List.reverse : List Bool → List Bool) hp TM2ListReverse.reverse_isPolyTime
  have he : (fun xs : List Bool => (output (folded (foldInput xs))).reverse) = payload := by
    funext xs
    change ((Shared.ComplexityBridge.TM2PolynomialFold.fold Source284ParseFoldStep.step
      ((false,false),[]) (xs ++ [false])).2).reverse = payload xs
    rw [fold_correct]
    simp
  rw [he] at hr
  exact hr

end Shared.Beeping.NPcoNP.Source284RawParseTM2
