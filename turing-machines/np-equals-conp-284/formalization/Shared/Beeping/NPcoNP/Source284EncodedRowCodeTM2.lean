import Shared.Beeping.NPcoNP.Source284EncodedRows
import Shared.Beeping.NPcoNP.Source284CompileRowTM2

set_option backward.isDefEq.respectTransparency false

/-! Construct the binary source record code of a finite encoded relative row.
The entire encoded row, including arbitrary binary destination values, is
charged. Terminal destinations are ignored; no unary expansion is performed. -/
namespace Shared.Beeping.NPcoNP.Source284EncodedRowCodeTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows

/-- Exact record semantics for the frozen encoded-row representation. -/
def code (r : EncRow) : Nat :=
  Shared.Beeping.NPcoNP.Source284TableEncode.rowCode (decodeRow r)

theorem code_isPolyTime : IsPolyTime code := by
  let tail : EncRow → Bool × Bool × Nat := fun r => r.2
  let last : EncRow → Bool × Nat := fun r => (tail r).2
  let write : EncRow → Bool := fun r => r.1
  let turn : EncRow → Bool := fun r => (tail r).1
  let continues : EncRow → Bool := fun r => (last r).1
  let dest : EncRow → Nat := fun r => (last r).2
  let next : EncRow → Nat := fun r => if continues r then 2*dest r+1 else 0
  have ht : IsPolyTime tail := TM2GuardAllStep.second_isPolyTime
  have hl : IsPolyTime last := TM2Compose.isPolyTime_comp tail
    (fun p : Bool × Bool × Nat => p.2) ht TM2GuardAllStep.second_isPolyTime
  have hw : IsPolyTime write := TM2PairFirst.first_isPolyTime
  have hturn : IsPolyTime turn := TM2Compose.isPolyTime_comp tail
    (fun p : Bool × Bool × Nat => p.1) ht TM2PairFirst.first_isPolyTime
  have hc : IsPolyTime continues := TM2Compose.isPolyTime_comp last
    (fun p : Bool × Nat => p.1) hl TM2PairFirst.first_isPolyTime
  have hd : IsPolyTime dest := TM2Compose.isPolyTime_comp last
    (fun p : Bool × Nat => p.2) hl TM2GuardAllStep.second_isPolyTime
  have hactive : IsPolyTime (fun r : EncRow => 2*dest r+1) := by
    have h := TM2Compose.isPolyTime_comp dest Shared.ComplexityBridge.CNFDisjunction.selector
      hd CNFBinaryIndex.selector_isPolyTime
    simpa [CNFDisjunction.selector] using h
  have hn : IsPolyTime next := TM2If.if_isPolyTime continues (fun r => 2*dest r+1)
    (fun _ => 0) hc hactive TM2EmptyConstant.zero_isPolyTime
  have hp := TM2GuardAllStep.pair_isPolyTime turn next hturn hn
  have hargs := TM2GuardAllStep.pair_isPolyTime write (fun r => (turn r,next r)) hw hp
  have h := TM2Compose.isPolyTime_comp (fun r => (write r,(turn r,next r)))
    (fun p : Bool × (Bool × Nat) => Shared.Beeping.NPcoNP.Source284CompileRecords.pack p.1 p.2.1 p.2.2)
    hargs Shared.Beeping.NPcoNP.Source284CompileRowTM2.pack_isPolyTime
  have he : (fun r : EncRow => Shared.Beeping.NPcoNP.Source284CompileRecords.pack
      (write r) (turn r) (next r)) = code := by
    funext r
    rcases r with ⟨w,t,c,n⟩
    cases c <;> rfl
  rw [he] at h
  exact h

end Shared.Beeping.NPcoNP.Source284EncodedRowCodeTM2
