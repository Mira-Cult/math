import Shared.Beeping.NPcoNP.Source284EncodedRows
import Shared.Beeping.NPcoNP.Source284HardwireTable
import Shared.ComplexityBridge.TM2GuardAllStep
import Shared.ComplexityBridge.CNFBinaryPairAdd

/-! Fixed-arity workers for building the paid fixed-input loader from an
explicit finite relative table. Natural fields are binary encoded; every
addition is performed by the canonical polynomial-time adder. These workers
make no validity or bound assumption on the destination. -/
namespace Shared.Beeping.NPcoNP.Source284HardwireEncodedWorkersTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows

/-- Construct a canonical row from independently computed fields. -/
theorem row_isPolyTime {α : Type} [BitstringEncoding α]
    (write turn continues : α → Bool) (dest : α → Nat)
    (hw : IsPolyTime write) (ht : IsPolyTime turn) (hc : IsPolyTime continues)
    (hd : IsPolyTime dest) :
    IsPolyTime (fun x => (write x,turn x,continues x,dest x) : α → EncRow) := by
  exact TM2GuardAllStep.pair_isPolyTime write (fun x => (turn x,continues x,dest x)) hw
    (TM2GuardAllStep.pair_isPolyTime turn (fun x => (continues x,dest x)) ht
      (TM2GuardAllStep.pair_isPolyTime continues dest hc hd))

/-- Relocate even a terminal row's ignored destination; this need not be
normalized, but it decodes to the same terminal transition. -/
def shiftEncoded (p : Nat × EncRow) : EncRow :=
  (p.2.1,p.2.2.1,p.2.2.2.1,p.1+p.2.2.2.2)

@[simp] theorem decode_shiftEncoded (d : Nat) (r : EncRow) :
    decodeRow (shiftEncoded (d,r)) =
      Shared.Beeping.NPcoNP.Source284HardwireTable.shiftRow d (decodeRow r) := by
  rcases r with ⟨w,t,c,n⟩
  cases c <;> rfl

theorem shiftEncoded_isPolyTime : IsPolyTime shiftEncoded := by
  let d : Nat × EncRow → Nat := fun p => p.1
  let r : Nat × EncRow → EncRow := fun p => p.2
  let tail : Nat × EncRow → Bool × Bool × Nat := fun p => (r p).2
  let last : Nat × EncRow → Bool × Nat := fun p => (tail p).2
  let w : Nat × EncRow → Bool := fun p => (r p).1
  let t : Nat × EncRow → Bool := fun p => (tail p).1
  let c : Nat × EncRow → Bool := fun p => (last p).1
  let q : Nat × EncRow → Nat := fun p => (last p).2
  have hd : IsPolyTime d := TM2PairFirst.first_isPolyTime
  have hr : IsPolyTime r := TM2GuardAllStep.second_isPolyTime
  have htail : IsPolyTime tail := TM2Compose.isPolyTime_comp r
    (fun p : EncRow => p.2) hr TM2GuardAllStep.second_isPolyTime
  have hlast : IsPolyTime last := TM2Compose.isPolyTime_comp tail
    (fun p : Bool × Bool × Nat => p.2) htail TM2GuardAllStep.second_isPolyTime
  have hw : IsPolyTime w := TM2Compose.isPolyTime_comp r
    (fun p : EncRow => p.1) hr TM2PairFirst.first_isPolyTime
  have ht : IsPolyTime t := TM2Compose.isPolyTime_comp tail
    (fun p : Bool × Bool × Nat => p.1) htail TM2PairFirst.first_isPolyTime
  have hc : IsPolyTime c := TM2Compose.isPolyTime_comp last
    (fun p : Bool × Nat => p.1) hlast TM2PairFirst.first_isPolyTime
  have hq : IsPolyTime q := TM2Compose.isPolyTime_comp last
    (fun p : Bool × Nat => p.2) hlast TM2GuardAllStep.second_isPolyTime
  have hsum : IsPolyTime (fun p => d p + q p) := by
    have h := TM2Compose.isPolyTime_comp (fun p => (d p,q p)) CNFBinaryPairAdd.addPair
      (TM2GuardAllStep.pair_isPolyTime d q hd hq) CNFBinaryPairAdd.addPair_isPolyTime
    simpa [CNFBinaryPairAdd.addPair] using h
  have h := row_isPolyTime w t c (fun p => d p+q p) hw ht hc hsum
  change IsPolyTime (fun p : Nat × EncRow =>
    (p.2.1,p.2.2.1,p.2.2.2.1,p.1+p.2.2.2.2))
  simpa [w, t, c, d, q, last, tail, r] using h

/-- Apply the same relocation to both read-symbol rows. -/
def shiftPair (p : Nat × (EncRow × EncRow)) : EncRow × EncRow :=
  (shiftEncoded (p.1,p.2.1), shiftEncoded (p.1,p.2.2))

theorem shiftPair_isPolyTime : IsPolyTime shiftPair := by
  let d : Nat × (EncRow × EncRow) → Nat := fun p => p.1
  let rs : Nat × (EncRow × EncRow) → EncRow × EncRow := fun p => p.2
  let a : Nat × (EncRow × EncRow) → EncRow := fun p => (rs p).1
  let b : Nat × (EncRow × EncRow) → EncRow := fun p => (rs p).2
  have hd : IsPolyTime d := TM2PairFirst.first_isPolyTime
  have hrs : IsPolyTime rs := TM2GuardAllStep.second_isPolyTime
  have ha : IsPolyTime a := TM2Compose.isPolyTime_comp rs
    (fun p : EncRow × EncRow => p.1) hrs TM2PairFirst.first_isPolyTime
  have hb : IsPolyTime b := TM2Compose.isPolyTime_comp rs
    (fun p : EncRow × EncRow => p.2) hrs TM2GuardAllStep.second_isPolyTime
  have h1 := TM2Compose.isPolyTime_comp (fun p => (d p,a p)) shiftEncoded
    (TM2GuardAllStep.pair_isPolyTime d a hd ha) shiftEncoded_isPolyTime
  have h2 := TM2Compose.isPolyTime_comp (fun p => (d p,b p)) shiftEncoded
    (TM2GuardAllStep.pair_isPolyTime d b hd hb) shiftEncoded_isPolyTime
  have h := TM2GuardAllStep.pair_isPolyTime (fun p => shiftEncoded (d p,a p))
    (fun p => shiftEncoded (d p,b p)) h1 h2
  change IsPolyTime (fun p : Nat × (EncRow × EncRow) =>
    (shiftEncoded (p.1,p.2.1),shiftEncoded (p.1,p.2.2)))
  simpa [d, a, b, rs] using h

end Shared.Beeping.NPcoNP.Source284HardwireEncodedWorkersTM2
