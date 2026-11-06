import Shared.Beeping.NPcoNP.Source284RecordListTM2
import Shared.ComplexityBridge.TM2BoundedUnary
import Shared.ComplexityBridge.TM2EmptyConstant

/-! Effective source-record serialization of a list of binary naturals with
an explicit unary budget. Values larger than the budget are clamped; equality
with the original record list requires the stated guard. No unrestricted
binary-to-unary conversion, table compiler, or NP-hardness result is claimed. -/
namespace Shared.Beeping.NPcoNP.Source284BoundedRecordListTM2

open Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284TableBits
open Shared.Beeping.NPcoNP.Source284RecordListTM2
open Shared.Codes.BitNumeralCompare (value)

abbrev Input := List Bool × List Nat

/-- All record expansions share the explicitly supplied unary budget. -/
def expanded (p : Input) : List (List Bool) :=
  TM2ContextMapGeneric.contextMap TM2BoundedUnary.expand p

def serialize (p : Input) : List Bool := unaryRecords (expanded p) []

/-- Every binary record is clipped by the supplied unary budget, so the raw
output contains at most one budget plus one delimiter per input record. -/
theorem serialize_length_le (budget : List Bool) (values : List Nat) :
    (serialize (budget, values)).length ≤ values.length * (budget.length + 1) := by
  simp only [serialize, unaryRecords_length, expanded, TM2ContextMapGeneric.contextMap,
    List.map_map, Function.comp_def, TM2BoundedUnary.expand_correct, List.length_replicate,
    List.length_nil, Nat.add_zero]
  induction values with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul] at *
    have hm : min a budget.length ≤ budget.length := Nat.min_le_right _ _
    omega

/-- The entire encoded output has an explicit quadratic bound in the full
canonical input encoding, not merely in the numeric record values. -/
theorem serialize_encoded_length_le (budget : List Bool) (values : List Nat) :
    (BitstringEncoding.bitEncode (serialize (budget, values))).length ≤
      3 * ((BitstringEncoding.bitEncode (budget, values)).length *
        ((BitstringEncoding.bitEncode (budget, values)).length + 1)) := by
  let size := (BitstringEncoding.bitEncode (budget, values)).length
  have hv : values.length ≤ size := by
    have h := Shared.ComplexityBridge.CNF.list_length_le_bitEncode values
    change values.length ≤ (BitstringEncoding.delimit (BitstringEncoding.bitEncode budget) ++
      BitstringEncoding.bitEncode values).length
    simp only [List.length_append, BitstringEncoding.length_delimit]
    omega
  have hb : budget.length ≤ size := by
    change budget.length ≤ (BitstringEncoding.delimit (BitstringEncoding.bitEncode budget) ++
      BitstringEncoding.bitEncode values).length
    simp only [List.length_append, BitstringEncoding.length_delimit, bitstring_list_encoded_length]
    omega
  have hm : values.length * (budget.length + 1) ≤ size * (size + 1) :=
    Nat.mul_le_mul hv (Nat.add_le_add_right hb 1)
  calc
    (BitstringEncoding.bitEncode (serialize (budget, values))).length =
        3 * (serialize (budget, values)).length := bitstring_list_encoded_length _
    _ ≤ 3 * (values.length * (budget.length + 1)) :=
      Nat.mul_le_mul_left 3 (serialize_length_le budget values)
    _ ≤ 3 * (size * (size + 1)) := Nat.mul_le_mul_left 3 hm

theorem expanded_isPolyTime : ComplexityTheory.IsPolyTime expanded :=
  TM2ContextMapGeneric.contextMap_isPolyTime TM2BoundedUnary.expand TM2BoundedUnary.expand_isPolyTime

/-- The construction is canonical polynomial time in the complete input
pair, including the unary budget and every binary record value. -/
theorem serialize_isPolyTime : ComplexityTheory.IsPolyTime serialize := by
  have he : ComplexityTheory.IsPolyTime (fun _ : Input => ([] : List Bool)) :=
    TM2EmptyConstant.isPolyTime ([] : List Bool) rfl
  have hp := TM2GuardAllStep.pair_isPolyTime expanded (fun _ : Input => ([] : List Bool))
    expanded_isPolyTime he
  exact TM2Compose.isPolyTime_comp (fun p : Input => (expanded p, ([] : List Bool)))
    (fun p : List (List Bool) × List Bool => unaryRecords p.1 p.2) hp unaryRecords_isPolyTime

/-- Explicitly account for clipping when a binary value exceeds the budget. -/
theorem serialize_value_clamped (budget : List Bool) (values : List Nat) :
    value (serialize (budget, values)) =
      encodeRecords (values.map (fun n => min n budget.length)) 0 := by
  simp [serialize, expanded, TM2ContextMapGeneric.contextMap, zeroTail_value,
    TM2BoundedUnary.expand_correct, List.map_map, Function.comp_def]

/-- Under the guard that every row value fits the unary budget, the literal
output denotes exactly the original list of source records. -/
theorem serialize_value (budget : List Bool) (values : List Nat)
    (h : ∀ n ∈ values, n ≤ budget.length) :
    value (serialize (budget, values)) = encodeRecords values 0 := by
  rw [serialize_value_clamped]
  congr 1
  calc
    values.map (fun n => min n budget.length) = values.map (fun n => n) := by
      apply List.map_congr_left
      intro n hn
      exact Nat.min_eq_left (h n hn)
    _ = values := by simp

end Shared.Beeping.NPcoNP.Source284BoundedRecordListTM2
