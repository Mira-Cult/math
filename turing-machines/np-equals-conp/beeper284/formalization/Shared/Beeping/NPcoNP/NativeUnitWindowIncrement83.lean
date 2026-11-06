import Shared.Beeping.NPcoNP.NativeUnitCarryExact83
import Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue

/-! A unit selector whose following value is zero composes with the
executable increment and finite return, without a graph-layout hypothesis. -/
namespace Shared.Beeping.NPcoNP.NativeUnitWindowIncrement83
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeUnit261Return1
open Shared.Beeping.NPcoNP.NativeUnitCarryExact83
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- A supplied unit window and nonempty scan word perform an increment and
return in exact finite silent time, retaining the updated bank. The final
carry segment takes `2*r+7` transitions. -/
theorem unit_window_increment_to83_exact (t : Int → Bool) (a : Int) (k z r v : Nat)
    (zs rest : List Nat)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ 1::0::z::zs)))
    (hr : 0<r)
    (pre : t (a+((2*k : Nat):Int)+3)=false)
    (scanword : Holds t (a+((2*k : Nat):Int)+6) (List.replicate r true ++ [false]))
    (bank : Holds t (a+((2*k : Nat):Int)+6+(r : Int)+1) (encode (v::rest) ++ [false])) :
    let d := a+((2*k : Nat):Int)+4
    let base := d+2+(r : Int)+1
    let values := (v+1)::rest
    ∃ mid : Config 284, mid.state=23 ∧
      Holds mid.tape base (encode values) ∧
      silentSegment machine (cfg 93 a t) mid (2*k+4+(r+v+6+(encode rest).length)) ∧
      let u := put (put mid.tape (d-1) true) (d+2) false
      let out := put (clearRange u (d+3) (d+2+(r : Int))) (d+1+(r : Int)) true
      Holds out base (encode values) ∧
      (∀ q, base≤q → out q=mid.tape q) ∧
      out (d-1)=true ∧ (∀ q, q<d-1 → out q=t q) ∧
      silentSegment machine mid (cfg 83 (d-2) out) ((encode values).length+r+2+(2*r+7)) := by
  dsimp only
  let d := a+((2*k : Nat):Int)+4
  let base := d+2+(r : Int)+1
  let values := (v+1)::rest
  have h261 := marker_window_to_one t a k (0::z::zs) (by simp) window
  obtain ⟨hone,hzeroWord⟩ := one_marker_tail t a k 0 z zs window
  have hzero : t (d+1)=false := by simpa [d] using hzeroWord.1
  have hpre : t (d-1)=false := by
    have he : d-1=a+((2*k : Nat):Int)+3 := by dsimp [d]; omega
    rw [he]
    exact pre
  have hscan : Holds t (d+2) (List.replicate r true ++ [false]) := by
    have he : d+2=a+((2*k : Nat):Int)+6 := by dsimp [d]; omega
    rw [he]
    exact scanword
  have hbank : Holds t base (encode (v::rest) ++ [false]) := by
    have he : base=a+((2*k : Nat):Int)+6+(r : Int)+1 := by dsimp [base,d]; omega
    rw [he]
    exact bank
  obtain ⟨mid,hs,hb,hmark,hframe,hinc,hret⟩ :=
    dispatch_increment_return1 r v rest d t hr hone hzero hscan hbank
  have hpre' : mid.tape (d-1)=false := by
    rw [hframe (d-1) (by omega) (Or.inl (by omega))]
    exact hpre
  have hzero' : mid.tape (d+1)=false := by
    rw [hframe (d+1) (by omega) (Or.inl (by omega))]
    exact hzero
  have hscan' : Holds mid.tape (d+2) (List.replicate r true ++ [false]) := by
    apply holds_transport t mid.tape _ _ hscan
    intro q hq hq'
    symm
    apply hframe q (by omega)
    left
    have hl : (List.replicate r true ++ [false]).length=r+1 := by simp
    rw [hl] at hq'
    omega
  let u := put (put mid.tape (d-1) true) (d+2) false
  let out := put (clearRange u (d+3) (d+2+(r : Int))) (d+1+(r : Int)) true
  have hcarry := carry_to83_exact r d mid.tape hr hpre' hmark hzero' hscan'
  have hright : ∀ q, base≤q → out q=mid.tape q := by
    intro q hq
    change put (clearRange u (d+3) (d+2+(r : Int))) (d+1+(r : Int)) true q=mid.tape q
    rw [put_other _ _ _ _ (by dsimp [base] at hq; omega)]
    change (if d+3≤q ∧ q<d+2+(r : Int) then false else u q)=mid.tape q
    rw [if_neg (by dsimp [base] at hq; omega)]
    change put (put mid.tape (d-1) true) (d+2) false q=mid.tape q
    rw [put_other _ _ _ _ (by dsimp [base] at hq; omega),
      put_other _ _ _ _ (by dsimp [base] at hq; omega)]
  have hout : Holds out base (encode values) := by
    apply holds_transport mid.tape out base _ hb
    intro q hq _
    symm
    exact hright q hq
  have hmarker : out (d-1)=true := by
    dsimp [out,u]
    rw [put_other _ _ _ _ (by omega)]
    change (if d+3≤d-1 ∧ d-1<d+2+(r : Int) then false else
      put (put mid.tape (d-1) true) (d+2) false (d-1))=true
    rw [if_neg (by omega),put_other _ _ _ _ (by omega)]
    simp [put]
  have hleft : ∀ q, q<d-1 → out q=t q := by
    intro q hq
    change put (clearRange u (d+3) (d+2+(r : Int))) (d+1+(r : Int)) true q=t q
    rw [put_other _ _ _ _ (by omega)]
    change (if d+3≤q ∧ q<d+2+(r : Int) then false else u q)=t q
    rw [if_neg (by omega)]
    change put (put mid.tape (d-1) true) (d+2) false q=t q
    rw [put_other _ _ _ _ (by omega),put_other _ _ _ _ (by omega)]
    exact hframe q (by omega) (Or.inl (by omega))
  refine ⟨mid,hs,hb,segAdd machine _ _ _ (2*k+4) (r+v+6+(encode rest).length) h261 hinc,
    hout,hright,hmarker,hleft,?_⟩
  exact segAdd machine _ _ _ ((encode values).length+r+2) (2*r+7) hret hcarry

#print axioms unit_window_increment_to83_exact
end Shared.Beeping.NPcoNP.NativeUnitWindowIncrement83
