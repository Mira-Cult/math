import Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
import Shared.Beeping.NPcoNP.NativeHalfState10Progress

/-! A value-two selector reaches state 42 on a one, avoiding state 10.
The source selector window is supplied, not proved reachable here. -/
namespace Shared.Beeping.NPcoNP.NativeHalfMarkerTwoSafe
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

theorem row260_zero : machine.table.row 260 false = ⟨true,.right,42,false⟩ := by decide
theorem row42_one : machine.table.row 42 true = ⟨false,.left,283,false⟩ := by decide

theorem step260_zero (h : Int) (t : Int → Bool) (hz : t h=false) :
    machine.step (cfg 260 h t)=(cfg 42 (h+1) (setAt h t),false) := by
  change machine.step ⟨260,h,t⟩=(⟨42,h+1,setAt h t⟩,false)
  have hw : (⟨260,h,t⟩ : Config 284).write true=setAt h t := rfl
  simp [Machine.step,hz,row260_zero,Move.apply,hw]

theorem step42_one (h : Int) (t : Int → Bool) (ho : t h=true) :
    machine.step (cfg 42 h t)=(cfg 283 (h-1) (put t h false),false) := by
  change machine.step ⟨42,h,t⟩=(⟨283,h-1,put t h false⟩,false)
  have hw : (⟨42,h,t⟩ : Config 284).write false=put t h false := rfl
  simp [Machine.step,ho,row42_one,Move.apply,hw]

/-- The value-two block's delimiter is followed by the first one of the
next encoded block, so state 42 reads one after state 260. -/
theorem two_marker_tail (t : Int → Bool) (a : Int) (k y z : Nat) (zs : List Nat)
    (hw : Holds t a (markerWindow (List.replicate k 0 ++ 2 :: y :: z :: zs))) :
    let d := a+((2*k : Nat) : Int)+4
    t d=false ∧ t (d+1)=true := by
  obtain ⟨tail,he⟩ := marker_two_blocks k 2 y z zs
  rw [he] at hw
  have hh := holds_append_tail t (a+1) (encode (List.replicate k 0))
    (block 2 ++ block y ++ tail) (by simpa [List.append_assoc] using hw.2)
  have hl : (encode (List.replicate k 0)).length=2*k := zeros_length k
  rw [hl] at hh
  simp only [block,List.replicate_succ,List.replicate_zero,List.nil_append,
    List.cons_append,Holds] at hh
  dsimp only
  have hpos : a+1+((2*k : Nat):Int)+1+1+1 = a+((2*k : Nat):Int)+4 := by omega
  rw [hpos] at hh
  exact ⟨hh.2.2.2.1,hh.2.2.2.2.1⟩

/-- The exact silent trace traverses state 260 and then state 42 with a
one, reaching state 283; it does not visit the state-10 branch. -/
theorem marker_two_to283 (t : Int → Bool) (a : Int) (k y z : Nat) (zs : List Nat)
    (hw : Holds t a (markerWindow (List.replicate k 0 ++ 2 :: y :: z :: zs))) :
    let d := a+((2*k : Nat) : Int)+4
    silentSegment machine (cfg 93 a t)
      (cfg 283 d (put (setAt d t) (d+1) false)) (2*k+6) := by
  dsimp only
  let d := a+((2*k : Nat) : Int)+4
  have h260 := marker_window_to_ge_two t a k 0 (y::z::zs) (by simp) hw
  have ht := two_marker_tail t a k y z zs hw
  change t d=false ∧ t (d+1)=true at ht
  have hs := oneSeg machine _ _ (step260_zero d t ht.1)
  have hnext : setAt d t (d+1)=true := by simp [setAt,ht.2]
  have h42 := oneSeg machine _ _ (step42_one (d+1) (setAt d t) hnext)
  have hall := segAdd machine _ _ _ (2*k+4+1) 1
    (segAdd machine _ _ _ (2*k+4) 1 h260 hs) h42
  simpa [d,Nat.add_assoc] using hall

#print axioms two_marker_tail
#print axioms marker_two_to283
end Shared.Beeping.NPcoNP.NativeHalfMarkerTwoSafe
