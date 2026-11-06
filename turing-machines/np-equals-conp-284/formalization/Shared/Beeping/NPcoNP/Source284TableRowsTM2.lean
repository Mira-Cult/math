import Shared.Beeping.NPcoNP.Source284BoundedRecordListTM2
import Shared.Beeping.NPcoNP.Source284TableSize
import Shared.Beeping.NPcoNP.Source284AcceptRecordEquiv
import Shared.ComplexityBridge.TM2CircuitOutputWorker

/-! Canonical polynomial-time source serialization of an explicit binary
list of row codes. The unary budget is built from the *number* of input
rows, not from unbounded numeric values. Invalid oversized rows are clipped;
closed finite tables satisfy the proved row bound and are serialized exactly.
This does not construct the row list from a table or prove SAT hardness. -/
namespace Shared.Beeping.NPcoNP.Source284TableRowsTM2

open Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284TableSize
open Shared.Beeping.NPcoNP.Source284BoundedRecordListTM2
open Shared.Codes.BitNumeralCompare (value)

def tokens (values : List Nat) : List Bool := values.map (fun _ => true)

/-- Four cells per encoded row and seven additional cells suffice for a
closed table's `8*n+7` row-code bound when the list has `2*n` rows. -/
def budget (values : List Nat) : List Bool :=
  TM2CircuitOutputWorker.copies 4 (tokens values) ++
    TM2CircuitOutputWorker.constantTokens 7 (tokens values)

theorem budget_length (values : List Nat) : (budget values).length = 4 * values.length + 7 := by
  simp [budget, tokens, TM2CircuitOutputWorker.copies_length,
    TM2CircuitOutputWorker.constantTokens_length]

theorem budget_isPolyTime : ComplexityTheory.IsPolyTime budget := by
  have ht : ComplexityTheory.IsPolyTime tokens := by
    exact TM2ContextMapGeneric.listMap_isPolyTime (fun _ : Nat => true) (TM2Constant.isPolyTime true)
  have hc : ComplexityTheory.IsPolyTime (fun values : List Nat =>
      TM2CircuitOutputWorker.copies 4 (tokens values)) :=
    TM2Compose.isPolyTime_comp tokens (TM2CircuitOutputWorker.copies 4) ht
      (TM2CircuitOutputWorker.copies_isPolyTime 4)
  have hs : ComplexityTheory.IsPolyTime (fun values : List Nat =>
      TM2CircuitOutputWorker.constantTokens 7 (tokens values)) :=
    TM2Compose.isPolyTime_comp tokens (TM2CircuitOutputWorker.constantTokens 7) ht
      (TM2CircuitOutputWorker.constantTokens_isPolyTime 7)
  exact TM2CircuitTemplate.append_isPolyTime _ _ hc hs

/-- A total serializer for any binary row-code list, with safe clipping for
out-of-budget values. Its input is the list itself. -/
def serializeRows (values : List Nat) : List Bool :=
  serialize (budget values, values)

theorem serializeRows_isPolyTime : ComplexityTheory.IsPolyTime serializeRows := by
  have hid : ComplexityTheory.IsPolyTime (id : List Nat → List Nat) :=
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hp := TM2GuardAllStep.pair_isPolyTime budget id budget_isPolyTime hid
  exact TM2Compose.isPolyTime_comp (fun values : List Nat => (budget values, values))
    serialize hp serialize_isPolyTime

/-- Any finite record-code list with each value bounded by the automatic
budget is serialized exactly; no table representation is assumed. -/
theorem serializeRows_correct (values : List Nat)
    (h : ∀ v ∈ values, v ≤ 4 * values.length + 7) :
    value (serializeRows values) = encodeRecords values 0 := by
  apply serialize_value
  intro v hv
  rw [budget_length]
  exact h v hv

/-- A zero-tail serialization and the same explicitly terminated records
with sentinel tail one agree on bounded acceptance, even if their final
accepting tape writes differ. -/
theorem serializeRows_sentinel_accepts (values : List Nat)
    (h : ∀ v ∈ values, v ≤ 4 * values.length + 7)
    (input certificate clock : Nat) :
    Source284Relative.accepts (value (serializeRows values)) input certificate clock =
      Source284Relative.accepts (encodeRecords values 1) input certificate clock := by
  rw [serializeRows_correct values h]
  exact accepts_eq_of_acceptRecordAgreement _ _ (sentinel_acceptRecordAgreement values)
    input certificate clock

/-- Every record generated from a closed n-state table fits the automatic
budget, so no clipping changes its value. -/
theorem records_fit (n : Nat) (table : Nat → Bool → Row)
    (closed : Closed n table) :
    ∀ v ∈ records n table, v ≤ (budget (records n table)).length := by
  intro v hv
  have h := records_bounded n table closed v hv
  rw [budget_length]
  have hl : (records n table).length = 2 * n := by simp [records]
  rw [hl]
  omega

/-- The computed bit list denotes the exact zero-tail numeric source code
when supplied the row-code list of a closed table. -/
theorem closed_table_correct (n : Nat) (table : Nat → Bool → Row)
    (closed : Closed n table) :
    value (serializeRows (records n table)) = encode n table 0 := by
  exact serialize_value (budget (records n table)) (records n table) (records_fit n table closed)

/-- At every finite clock, the serialized closed-table row list has exactly
the same bounded acceptance as the original relative table. -/
theorem closed_table_acceptance (n : Nat) (table : Nat → Bool → Row)
    (hn : 0 < n) (closed : Closed n table) (input certificate clock : Nat) :
    Source284Relative.accepts (value (serializeRows (records n table))) input certificate clock =
      (Source284TableRun.run table ⟨certificate, input, some 0⟩ clock).state.isNone := by
  rw [closed_table_correct n table closed]
  exact Source284TableRun.bounded_acceptance n table 0 hn closed input certificate clock

end Shared.Beeping.NPcoNP.Source284TableRowsTM2
