import Shared.Beeping.NPcoNP.Source284ScannerPackedStep
import Shared.Beeping.NPcoNP.Source284ScannerFoldBounds
import Shared.ComplexityBridge.TM2FoldGenericBounds
import Shared.ComplexityBridge.TM2BinaryListLength

/-! Canonical polynomial-time source-record lookup from raw binary lists.
The source program and binary ordinal are both explicit input. All intermediate
fold states have a proved linear bound in their full input encoding. This does
not implement the complete source evaluator or prove a class inclusion. -/
namespace Shared.Beeping.NPcoNP.Source284RecordTM2

open Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284RecordBitCost

abbrev Packed := Source284ScannerPackedStep.Packed

theorem fold_isPolyTime : ComplexityTheory.IsPolyTime
    (TM2FoldGenericIO.result Source284ScannerPackedStep.step) := by
  apply TM2FoldGenericBounds.isPolyTime_of_prefix_bound
    Source284ScannerPackedStep.step Source284ScannerPackedStep.step_isPolyTime
  refine ⟨Polynomial.X, ?_⟩
  intro init xs pref tail hxs
  rcases init with ⟨d,idx⟩
  have hp : pref.length ≤ xs.length := by rw [hxs, List.length_append]; omega
  simp only [Polynomial.eval_X]
  rw [Source284ScannerPackedStep.fold_transport]
  change (BitstringEncoding.bitEncode (Source284ScannerFoldBounds.packed
    (TM2PolynomialFold.fold Source284ScannerFoldStep.step (d,(idx,[])) pref))).length ≤ _
  exact Source284ScannerFoldBounds.initial_packed_bound_of_length d idx pref xs hp

/-- Code and ordinal are arbitrary raw low-endian lists, including redundant
high zeroes. The scanner emits one unary cell for each one in the record. -/
def scanInput (p : List Bool × List Bool) : (Bool × List Bool) × List Bool :=
  ((false,p.2),p.1)

theorem scanInput_isPolyTime : ComplexityTheory.IsPolyTime scanInput := by
  let code : List Bool × List Bool → List Bool := fun p => p.1
  let idx : List Bool × List Bool → List Bool := fun p => p.2
  let init : List Bool × List Bool → Bool × List Bool := fun p => (false,idx p)
  have hc : ComplexityTheory.IsPolyTime code := TM2PairFirst.first_isPolyTime
  have hi : ComplexityTheory.IsPolyTime idx := TM2GuardAllStep.second_isPolyTime
  have hz : ComplexityTheory.IsPolyTime (fun _ : List Bool × List Bool => false) := TM2Constant.isPolyTime false
  have hinit : ComplexityTheory.IsPolyTime init :=
    TM2GuardAllStep.pair_isPolyTime (fun _ : List Bool × List Bool => false) idx hz hi
  exact TM2GuardAllStep.pair_isPolyTime init code hinit hc

theorem scan_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : List Bool × List Bool => scan p.1 p.2) := by
  let folded := TM2FoldGenericIO.result Source284ScannerPackedStep.step
  let output : Packed → List Bool := fun p => p.2
  have houtput : ComplexityTheory.IsPolyTime output := TM2GuardAllStep.second_isPolyTime
  have hf := TM2Compose.isPolyTime_comp scanInput folded scanInput_isPolyTime fold_isPolyTime
  have ho := TM2Compose.isPolyTime_comp (fun p => folded (scanInput p)) output hf houtput
  have hr := TM2Compose.isPolyTime_comp (fun p => output (folded (scanInput p)))
    (List.reverse : List Bool → List Bool) ho TM2ListReverse.reverse_isPolyTime
  have he : (fun p : List Bool × List Bool => (output (folded (scanInput p))).reverse) =
      (fun p => scan p.1 p.2) := by
    funext p
    rcases p with ⟨code,idx⟩
    exact Source284ScannerPackedStep.fold_correct code idx
  rw [he] at hr
  exact hr

/-- Return the record as a natural number in the canonical binary encoding,
avoiding an additional unary-to-binary data converter. -/
def lookup (p : List Bool × List Bool) : Nat := (scan p.1 p.2).length

theorem lookup_isPolyTime : ComplexityTheory.IsPolyTime lookup :=
  TM2Compose.isPolyTime_comp (fun p : List Bool × List Bool => scan p.1 p.2)
    (List.length : List Bool → Nat) scan_isPolyTime TM2BinaryListLength.length_isPolyTime

theorem lookup_correct (code idx : List Bool) :
    lookup (code,idx) = Source284Relative.record
      (Shared.Codes.BitNumeralCompare.value code) (Shared.Codes.BitNumeralCompare.value idx) := by
  rw [lookup, scan_correct, ← Source284RecordBits.recordBits_correct]

end Shared.Beeping.NPcoNP.Source284RecordTM2
