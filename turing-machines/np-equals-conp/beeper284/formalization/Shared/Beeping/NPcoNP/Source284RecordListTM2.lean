import Shared.ComplexityBridge.TM2ContextMapGeneric
import Shared.ComplexityBridge.TM2FlattenList
import Shared.ComplexityBridge.TM2CircuitTemplate
import Shared.ComplexityBridge.TM2Constant
import Shared.ComplexityBridge.Encodings
import Shared.Beeping.NPcoNP.Source284TableBits

/-! Canonical polynomial-time serialization of explicitly unary source-record
values. Each input row is a bit list whose length is the value; its contents
are ignored. The output consists of that many ones and a zero delimiter for
each row, followed by the supplied arbitrary finite high tail. This does not
turn arbitrary binary numerals into unary in
polynomial time, serialize finite transition tables, or prove SAT hardness. -/

namespace Shared.Beeping.NPcoNP.Source284RecordListTM2

open Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284TableBits

/-- Delimiters in the canonical nested-list input already pay for every raw
serialized record bit. -/
theorem body_length_le_input (rows : List (List Bool)) :
    ((rows.map recordWord).flatten).length ≤ (BitstringEncoding.bitEncode rows).length := by
  induction rows with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.flatten_cons, List.length_append,
      TM2MapSizeBounds.encode_cons, List.length_append, BitstringEncoding.length_delimit,
      recordWord_length, bitstring_list_encoded_length]
    omega

/-- The output's canonical encoding is at most three times the complete
canonical pair input, including all unary row values and the high tail. -/
theorem output_encoding_le (p : List (List Bool) × List Bool) :
    (BitstringEncoding.bitEncode (unaryRecords p.1 p.2)).length ≤
      3 * (BitstringEncoding.bitEncode p).length := by
  rcases p with ⟨rows, tail⟩
  have hb := body_length_le_input rows
  rw [bitstring_list_encoded_length]
  change 3 * (unaryRecords rows tail).length ≤
    3 * (BitstringEncoding.delimit (BitstringEncoding.bitEncode rows) ++
      BitstringEncoding.bitEncode tail).length
  simp only [unaryRecords, List.length_append, BitstringEncoding.length_delimit,
    bitstring_list_encoded_length]
  omega

/-- Mapping a unary-sized input block to the required delimiter-terminated
record is a genuine polynomial-time computation in the canonical model. -/
theorem recordWord_isPolyTime : ComplexityTheory.IsPolyTime recordWord := by
  have hm : ComplexityTheory.IsPolyTime (fun xs : List Bool => xs.map (fun _ => true)) :=
    TM2ContextMapGeneric.listMap_isPolyTime (fun _ : Bool => true) (TM2Constant.isPolyTime true)
  have hd : ComplexityTheory.IsPolyTime (fun _ : List Bool => [false]) :=
    TM2GateCNFPieces.singleton_isPolyTime (fun _ : List Bool => false) (TM2Constant.isPolyTime false)
  change ComplexityTheory.IsPolyTime (fun xs : List Bool => xs.map (fun _ => true) ++ [false])
  exact TM2CircuitTemplate.append_isPolyTime (fun xs : List Bool => xs.map (fun _ => true))
    (fun _ => [false]) hm hd

/-- The complete variable-length record list is constructed by finite TM2
list map and flatten, with every unary row included in the encoded input. -/
theorem unaryRecords_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : List (List Bool) × List Bool => unaryRecords p.1 p.2) := by
  let first : List (List Bool) × List Bool → List (List Bool) := fun p => p.1
  let second : List (List Bool) × List Bool → List Bool := fun p => p.2
  let mapped : List (List Bool) → List (List Bool) := fun rows => rows.map recordWord
  let body : List (List Bool) × List Bool → List Bool := fun p => (mapped (first p)).flatten
  have hf : ComplexityTheory.IsPolyTime first := TM2PairFirst.first_isPolyTime
  have hs : ComplexityTheory.IsPolyTime second := TM2GuardAllStep.second_isPolyTime
  have hm : ComplexityTheory.IsPolyTime mapped :=
    TM2ContextMapGeneric.listMap_isPolyTime recordWord recordWord_isPolyTime
  have hmap : ComplexityTheory.IsPolyTime (fun p => mapped (first p)) :=
    TM2Compose.isPolyTime_comp first mapped hf hm
  have hb : ComplexityTheory.IsPolyTime body :=
    TM2Compose.isPolyTime_comp (fun p => mapped (first p))
      (List.flatten : List (List Bool) → List Bool) hmap TM2FlattenList.flatten_isPolyTime
  simpa [unaryRecords, body, mapped, first, second] using
    TM2CircuitTemplate.append_isPolyTime body second hb hs

end Shared.Beeping.NPcoNP.Source284RecordListTM2
