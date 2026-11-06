import Shared.Beeping.NPcoNP.Source284HardwireGuardRows
import Shared.Beeping.NPcoNP.Source284HardwireIndexedTM2

/-! Canonical polynomial-time composition of the unary-cutoff countdown
constructor with the paid finite hardwired-input loader. Its input includes
all input bits, every cutoff token, and the full explicit original row list. -/
namespace Shared.Beeping.NPcoNP.Source284HardwireGuardRowsTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284HardwireGuardRows

/-- The entire guarded table is constructed from explicit finite data by a
canonical polynomial-time machine, including malformed original tables. -/
theorem rows_isPolyTime : IsPolyTime (fun p : List Bool × (List Bool × EncRows) =>
    rows p.1 p.2.1 p.2.2) := by
  let bits : List Bool × (List Bool × EncRows) → List Bool := fun p => p.1
  let guardInput : List Bool × (List Bool × EncRows) → List Bool × EncRows := fun p => p.2
  let guarded : List Bool × (List Bool × EncRows) → EncRows := fun p =>
    Source284GuardTableListTM2.tableRows (guardInput p)
  have hb : IsPolyTime bits := TM2PairFirst.first_isPolyTime
  have hi : IsPolyTime guardInput := TM2GuardAllStep.second_isPolyTime
  have hg : IsPolyTime guarded := TM2Compose.isPolyTime_comp guardInput
    Source284GuardTableListTM2.tableRows hi Source284GuardTableListTM2.tableRows_isPolyTime
  have ha := TM2GuardAllStep.pair_isPolyTime bits guarded hb hg
  have h := TM2Compose.isPolyTime_comp (fun p => (bits p,guarded p))
    (fun p : List Bool × EncRows => Source284HardwireIndexedList.rows p.1 p.2)
    ha Source284HardwireIndexedTM2.rows_isPolyTime
  change IsPolyTime (fun p : List Bool × (List Bool × EncRows) =>
    Source284HardwireIndexedList.rows p.1 (Source284GuardTableListTM2.tableRows p.2))
  simpa [bits,guardInput,guarded] using h

end Shared.Beeping.NPcoNP.Source284HardwireGuardRowsTM2
