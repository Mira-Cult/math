import Shared.Beeping.NPcoNP.NativeHalfMarkerTwoSafe
import Shared.Beeping.NPcoNP.NativeHalfState16Progress

/-! Complete positive selector dispatch on a supplied marker window. -/
namespace Shared.Beeping.NPcoNP.NativeHalfMarkerMany
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfMarkerTwoSafe
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

theorem row260_one : machine.table.row 260 true = ⟨false,.right,15,false⟩ := by decide

theorem step260_one (h : Int) (t : Int → Bool) (ho : t h=true) :
    machine.step (cfg 260 h t)=(cfg 15 (h+1) (clearAt h t),false) := by
  change machine.step ⟨260,h,t⟩=(⟨15,h+1,clearAt h t⟩,false)
  have hw : (⟨260,h,t⟩ : Config 284).write false=clearAt h t := rfl
  simp [Machine.step,ho,row260_one,Move.apply,hw]

/-- A selector value at least three has another one at the state-260 head. -/
theorem many_marker_head (t : Int → Bool) (a : Int) (k x y z : Nat) (zs : List Nat)
    (hw : Holds t a (markerWindow (List.replicate k 0 ++ (x+3) :: y :: z :: zs))) :
    t (a+((2*k : Nat) : Int)+4)=true := by
  obtain ⟨tail,he⟩ := marker_two_blocks k (x+3) y z zs
  rw [he] at hw
  have hh := holds_append_tail t (a+1) (encode (List.replicate k 0))
    (block (x+3) ++ block y ++ tail) (by simpa [List.append_assoc] using hw.2)
  have hl : (encode (List.replicate k 0)).length=2*k := zeros_length k
  rw [hl] at hh
  have hb : Holds t (a+1+((2*k : Nat):Int)) (block (x+3)) := by
    apply holds_prefix_word t _ _ (block y ++ tail)
    simpa [List.append_assoc] using hh
  have hi : 3<(block (x+3)).length := by simp [block_length]
  have ht := holds_get t _ (block (x+3)) hb 3 hi
  have hp : a+1+((2*k : Nat):Int)+(3:Int)=a+((2*k : Nat):Int)+4 := by omega
  norm_num only [Nat.cast_ofNat] at ht
  rw [hp] at ht
  simpa [block] using ht

/-- Values at least three dispatch through the state-260 one row to 15. -/
theorem marker_many_to15 (t : Int → Bool) (a : Int) (k x y z : Nat) (zs : List Nat)
    (hw : Holds t a (markerWindow (List.replicate k 0 ++ (x+3) :: y :: z :: zs))) :
    let d := a+((2*k : Nat) : Int)+4
    silentSegment machine (cfg 93 a t) (cfg 15 (d+1) (clearAt d t)) (2*k+5) := by
  dsimp only
  let d := a+((2*k : Nat) : Int)+4
  have h260 := marker_window_to_ge_two t a k (x+1) (y::z::zs) (by simp) (by
    simpa [Nat.add_assoc] using hw)
  have hone := many_marker_head t a k x y z zs hw
  have hs := oneSeg machine _ _ (step260_one d t hone)
  have hall := segAdd machine _ _ _ (2*k+4) 1 h260 hs
  simpa [d,Nat.add_assoc] using hall

/-- In the value-two case, the actual state-42 configuration is reached
with a one under its head, and the path to it is silent and finite. -/
theorem marker_two_at42 (t : Int → Bool) (a : Int) (k y z : Nat) (zs : List Nat)
    (hw : Holds t a (markerWindow (List.replicate k 0 ++ 2 :: y :: z :: zs))) :
    let d := a+((2*k : Nat) : Int)+4
    let c := cfg 42 (d+1) (setAt d t)
    c.tape c.head=true ∧ silentSegment machine (cfg 93 a t) c (2*k+5) := by
  dsimp only
  let d := a+((2*k : Nat) : Int)+4
  have h260 := marker_window_to_ge_two t a k 0 (y::z::zs) (by simp) hw
  have ht := two_marker_tail t a k y z zs hw
  change t d=false ∧ t (d+1)=true at ht
  have h42 : (setAt d t) (d+1)=true := by simp [setAt,ht.2]
  refine ⟨h42,?_⟩
  have hall := segAdd machine _ _ _ (2*k+4) 1 h260
    (oneSeg machine _ _ (step260_zero d t ht.1))
  simpa [d,Nat.add_assoc] using hall

#print axioms marker_two_at42
/-- All positive control values dispatch to the exact next literal state.
The value-two branch alone passes through state 42, where its read is one. -/
theorem marker_positive_dispatch (t : Int → Bool) (a : Int) (k v y z : Nat) (zs : List Nat)
    (hv : 0<v)
    (hw : Holds t a (markerWindow (List.replicate k 0 ++ v :: y :: z :: zs))) :
    let d := a+((2*k : Nat) : Int)+4
    let target := if v=1 then (16 : Fin 284) else if v=2 then 283 else 15
    let head := if v=2 then d else d+1
    let out := if v=2 then put (setAt d t) (d+1) false else clearAt d t
    silentSegment machine (cfg 93 a t) (cfg target head out)
      (2*k+(if v=2 then 6 else 5)) := by
  dsimp only
  cases v with
  | zero => omega
  | succ v =>
    cases v with
    | zero =>
      have h260 := marker_window_to_one t a k (y::z::zs) (by simp) hw
      have hone := (one_marker_tail t a k y z zs hw).1
      have hs := oneSeg machine _ _ (step261_one _ t hone)
      have hall := segAdd machine _ _ _ (2*k+4) 1 h260 hs
      simpa [Nat.add_assoc] using hall
    | succ v =>
      cases v with
      | zero => simpa using marker_two_to283 t a k y z zs hw
      | succ v =>
        have hh : Holds t a (markerWindow (List.replicate k 0 ++ (v+3) :: y :: z :: zs)) := by
          simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hw
        have hs := marker_many_to15 t a k v y z zs hh
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs

#print axioms marker_positive_dispatch
#print axioms many_marker_head
#print axioms marker_many_to15
end Shared.Beeping.NPcoNP.NativeHalfMarkerMany
