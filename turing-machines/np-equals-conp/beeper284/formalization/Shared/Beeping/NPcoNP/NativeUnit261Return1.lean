import Shared.Beeping.NPcoNP.NativeUnit261Increment
import Shared.Beeping.NPcoNP.NativeIncReturn23

/-! A parameterized unit dispatch, increment, and return to state 1. -/
namespace Shared.Beeping.NPcoNP.NativeUnit261Return1
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch
open Shared.Beeping.NPcoNP.NativeHalfReturn23
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeIncSelected
open Shared.Beeping.NPcoNP.NativeIncReturn23
open Shared.Beeping.NPcoNP.NativeUnit261Increment
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- A nonempty one-run gives state 23 a zero-pair-free path through the
updated bank and back to the pair created by the unit dispatch. -/
theorem dispatch_increment_return1 (r v : Nat) (rest : List Nat) (h : Int) (t : Int → Bool)
    (hr : 0<r) (hone : t h=true) (hzero : t (h+1)=false)
    (scanword : Holds t (h+2) (List.replicate r true ++ [false]))
    (bank : Holds t (h+2+(r : Int)+1) (encode (v::rest) ++ [false])) :
    let base := h+2+(r : Int)+1
    let values := (v+1)::rest
    ∃ mid : Config 284, mid.state=23 ∧
      Holds mid.tape base (encode values) ∧ mid.tape h=false ∧
      (∀ p, p≠h → (p<base ∨ base+(((v+1)+(encode rest).length : Nat):Int)<p) → mid.tape p=t p) ∧
      silentSegment machine (cfg 261 h t) mid (r+v+6+(encode rest).length) ∧
      silentSegment machine mid (cfg 1 (h-1) mid.tape) ((encode values).length+r+2) := by
  dsimp only
  let base := h+2+(r : Int)+1
  let values := (v+1)::rest
  obtain ⟨mid,hstate,hhead,hbank,hmark,hframe,hfirst⟩ :=
    dispatch_increment r v rest h t hone hzero scanword bank
  obtain ⟨front,hfront⟩ := encode_ends_zero values (by simp [values])
  have hlen : (encode values).length=front.length+1 := by rw [hfront]; simp
  have hprefix : Prefix (false::front.reverse) := by
    have ht := prefix_reverse_bank values
    rw [hfront] at ht
    simpa using ht
  have hpfront : Prefix front.reverse := prefix_tail_after_zero _ hprefix
  have hptail : Prefix (false::List.replicate r true) := by
    cases r with
    | zero => omega
    | succ n =>
      simp only [List.replicate_succ]
      exact Prefix.zeroOne (prefix_ones n)
  obtain ⟨shape,hshape⟩ := shape_of_prefix
    (front.reverse ++ (false::List.replicate r true)) (prefix_append hpfront hptail)
  have hword : Holds mid.tape base front := by
    have hh : Holds mid.tape base (front++[false]) := by rw [←hfront]; exact hbank
    exact holds_prefix mid.tape base front [false] hh
  have hreverse := holds_reverse mid.tape base front hword
  have hscanword : Holds mid.tape (h+2) (List.replicate r true ++ [false]) := by
    apply holds_transport t mid.tape _ _ scanword
    intro p hp hp'
    symm
    apply hframe p (by omega)
    left
    have hl : (List.replicate r true ++ [false]).length=r+1 := by simp
    rw [hl] at hp'
    omega
  have hscanrev := holds_reverse mid.tape (h+2) (List.replicate r true ++ [false]) hscanword
  have hstart : h+2+(((List.replicate r true ++ [false]).length : Nat):Int)-1=base-1 := by
    simp [base]
    omega
  rw [hstart] at hscanrev
  have hscanrev' : downHolds mid.tape (base-1) (false::List.replicate r true) := by
    simpa using hscanrev
  have hzero' : mid.tape (h+1)=false := by
    rw [hframe (h+1) (by omega) (Or.inl (by omega))]
    exact hzero
  have hzeros : downHolds mid.tape (h+1) [false,false] := by
    change mid.tape (h+1)=false ∧ mid.tape (h+1-1)=false ∧ True
    have he : h+1-1=h := by omega
    exact ⟨hzero',by rw [he]; exact hmark,trivial⟩
  have htail : downHolds mid.tape (base-1) ((false::List.replicate r true)++[false,false]) := by
    apply down_append mid.tape _ (false::List.replicate r true) [false,false] hscanrev'
    have he : base-1-(((false::List.replicate r true).length : Nat):Int)=h+1 := by
      simp [base]
      omega
    rw [he]
    exact hzeros
  have hall : downHolds mid.tape (base+(front.length : Int)-1)
      ((front.reverse ++ (false::List.replicate r true)) ++ [false,false]) := by
    have he : base+(front.length : Int)-1-((front.reverse.length : Nat):Int)=base-1 := by simp; omega
    have ht := down_append mid.tape _ front.reverse
      ((false::List.replicate r true)++[false,false]) hreverse (by rw [he]; exact htail)
    simpa only [List.append_assoc] using ht
  rw [←hshape] at hall
  have hret := return_scan shape (base+(front.length : Int)-1) mid.tape hall
  have hshapeLen : (bits shape).length=front.length+1+r := by
    rw [hshape]
    simp only [List.length_append,List.length_reverse,List.length_cons,List.length_replicate]
    omega
  have hstartmid : mid.head=base+(front.length : Int)-1 := by
    rw [hhead]
    dsimp [values] at hlen
    simp only [encode,block_length,List.length_append,Nat.cast_add] at hlen ⊢
    push_cast
    omega
  have hend : base+(front.length : Int)-1-((bits shape).length : Int)-2=h-1 := by
    rw [hshapeLen]
    dsimp [base]
    push_cast
    omega
  have hcost : (bits shape).length+2=(encode values).length+r+2 := by omega
  rw [hend,←hstartmid,hcost] at hret
  have hmid : mid=cfg 23 mid.head mid.tape := by
    have hi : mid=cfg mid.state mid.head mid.tape := by cases mid; rfl
    simpa only [hstate] using hi
  rw [←hmid] at hret
  exact ⟨mid,hstate,hbank,hmark,hframe,hfirst,hret⟩

#print axioms dispatch_increment_return1
end Shared.Beeping.NPcoNP.NativeUnit261Return1
