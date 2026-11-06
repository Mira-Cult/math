import Shared.Beeping.NPcoNP.NativeHalfEntryAllBanks
import Shared.Beeping.NPcoNP.NativeHalfState1Canonical
import Shared.Beeping.NPcoNP.NativeHalfState1FiniteSupport
import Shared.Beeping.NPcoNP.NativeHalfState27Scan

/-! Finite silent continuation from the selected native-HALF entry through
the literal state-1 carry and state-27 scan. Graph reachability and control
interpretation are separate obligations. -/
namespace Shared.Beeping.NPcoNP.NativeHalfEntryTo28

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState1FiniteSupport
open Shared.Beeping.NPcoNP.NativeHalfState27Scan
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.NativeHalfEntryCorrect
open Shared.Beeping.NPcoNP.NativeHalfEntryAllBanks
open Shared.Beeping.NPcoNP.NativeHalfState1Canonical
open Shared.Beeping.NPcoNP.NativeHalfReturn23BankExact
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

/-- A nonempty encoded bank begins with a one. -/
theorem encoded_head (t : Int → Bool) (h : Int) (values : List Nat)
    (hn : values≠[]) (ht : Holds t h (encode values)) : t h=true := by
  cases values with
  | nil => contradiction
  | cons v vs =>
    simpa [encode,block,List.replicate_succ,Holds] using ht.1

/-- Given a finite left delimiter and a zero corridor to the first bank
one, the carry and rightward scan reach state 28 in finite silent time.
The output is the exact paid tape update. -/
theorem state1_header_dispatch (t : Int → Bool) (h ctrl z : Int)
    (hh : h<ctrl) (hz : ∀ p≤z, t p=false)
    (hzeros : ∀ p, h+1≤p → p≤ctrl+1 → t p=false)
    (hone : t (ctrl+2)=true) :
    ∃ (n k : Nat), 0<n ∧
      downHolds t h (List.replicate k true ++ [false]) ∧
      silentSegment machine (cfg 1 h t)
        (cfg 28 (ctrl+3) (put (result t h k) (ctrl+2) false)) n := by
  let d := (h-min z h).toNat
  have hd : h-(d : Int)≤z := by
    have hn : 0≤h-min z h := by omega
    have he : (d : Int)=h-min z h := Int.toNat_of_nonneg hn
    omega
  obtain ⟨k,_,hcarry⟩ := first_zero d h t (hz _ hd)
  let start := h-(k : Int)+1
  let len := (ctrl+2-start).toNat
  have hlen : (len : Int)=ctrl+2-start := Int.toNat_of_nonneg (by dsimp [start]; omega)
  have hzc : ∀ i : Nat, i<len → result t h k (start+(i : Int))=false := by
    intro i hi
    let p := start+(i : Int)
    have hlo : h-(k : Int)<p := by dsimp [p,start]; omega
    have hhi : p<ctrl+2 := by dsimp [p]; omega
    have hne : p≠h-(k : Int) := by omega
    by_cases hp : p≤h
    · change (put (cleared t h k) (h-(k : Int)) true) p=false
      simp [put,cleared,hne,hlo,hp]
    · have ht : t p=false := hzeros p (by omega) (by omega)
      have hout : ¬ (h-(k : Int)<p ∧ p≤h) := by omega
      change (put (cleared t h k) (h-(k : Int)) true) p=false
      simp [put,cleared,hne,hout,ht]
  have hoc : result t h k (start+(len : Int))=true := by
    have he : start+(len : Int)=ctrl+2 := by omega
    rw [he]
    have hne : ctrl+2≠h-(k : Int) := by omega
    have hout : ¬ (h-(k : Int)<ctrl+2 ∧ ctrl+2≤h) := by omega
    simp [result,put,cleared,hne,hout,hone]
  have hfirst := NativeHalfState1Scan.scan t h k hcarry
  have hsecond := scan_to_one start (result t h k) len hzc hoc
  have hall := segAdd machine _ _ _ (k+1) (len+1) hfirst hsecond
  have hp : start+(len : Int)+1=ctrl+3 := by omega
  have hp' : start+(len : Int)=ctrl+2 := by omega
  refine ⟨(k+1)+(len+1),k,by omega,hcarry,?_⟩
  rw [hp,hp'] at hall
  exact hall

/-- Every prepared selected entry completes the native HALF work and the
following state-1/state-27 dispatch. The intermediate bank and both parity
control effects are exposed; no blank-start reachability is asserted. -/
theorem selected_entry_to28 (back : Int → Bool) (ctrl z : Int)
    (value : Nat) (left right : List Nat) (hz : ∀ p≤z, back p=false) :
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    let values := left ++ [value/2] ++ right ++ List.replicate ((value+1)/2) 0
    ∃ (n k : Nat) (head : Int) (t : Int → Bool), 0<n ∧
      (value%2=1 → head=ctrl-1) ∧ (value%2=0 → head≤ctrl-2) ∧
      (value%2=0 → back (head+1)=false) ∧
      (value%2=0 → ∀ p, head+1<p → p<ctrl → back p=true) ∧
      (∀ p, head+1≤p → p≤ctrl+1 → t p=false) ∧
      Holds t (ctrl+2) (encode values) ∧
      t=state1Tape back ctrl head values ∧
      t (ctrl+3+((encode values).length : Int))=false ∧
      (∀ p≤head, t p=back p) ∧
      downHolds back head (List.replicate k true ++ [false]) ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right))
        (cfg 28 (ctrl+3) (put (result t head k) (ctrl+2) false)) n := by
  dsimp only
  obtain ⟨n,head,t,hn,hodd,heven,hstopBack,honesBack,hclear,hoddback,hevenback,hstop,hctrl,hctrl1,
    hbank,hr0,hreserve,htail0,hfirst⟩ := selected_entry_packed_bank back ctrl z value left right hz
  have hcanonical := tape_eq_state1Tape_of_parity back ctrl head value _ t hodd hclear
    hoddback hevenback hctrl hctrl1 hbank hr0 hreserve htail0
  have hlt : head<ctrl := by
    by_cases hp : value%2=0
    · have h := heven hp
      omega
    · have hp' : value%2=1 := by omega
      have h := hodd hp'
      omega
  have htail : ∀ p≤min z (head-1), t p=false := by
    intro p hp
    have hpz : p≤z := le_trans hp (min_le_left _ _)
    have hph : p≤head-1 := le_trans hp (min_le_right _ _)
    by_cases hv : value%2=0
    · rw [hevenback hv p (by omega)]
      exact hz p hpz
    · have hv' : value%2=1 := by omega
      rw [hoddback hv' p (by omega)]
      exact hz p hpz
  have hzeros : ∀ p, head+1≤p → p≤ctrl+1 → t p=false := by
    intro p hp hp'
    by_cases h1 : p=head+1
    · simpa [h1] using hstop
    by_cases h2 : p=ctrl
    · simpa [h2] using hctrl
    by_cases h3 : p=ctrl+1
    · simpa [h3] using hctrl1
    by_cases hv : value%2=0
    · exact hclear hv p (by omega) (by omega)
    · have hv' : value%2=1 := by omega
      have hphead := hodd hv'
      omega
  have hnonempty : left ++ [value/2] ++ right ++ List.replicate ((value+1)/2) 0 ≠ [] := by
    simp
  have hone := encoded_head t (ctrl+2) _ hnonempty hbank
  obtain ⟨ksteps,k,hk,hcarry,hsecond⟩ := state1_header_dispatch t head ctrl (min z (head-1)) hlt htail hzeros hone
  have hprefix : ∀ p≤head, t p=back p := by
    intro p hp
    by_cases hv : value%2=0
    · exact hevenback hv p (by omega)
    · have hv' : value%2=1 := by omega
      exact hoddback hv' p (by omega)
  have hbackcarry : downHolds back head (List.replicate k true ++ [false]) := by
    apply down_congr back t head _ ?_ hcarry
    intro p hp
    exact (hprefix p hp).symm
  exact ⟨n+ksteps,k,head,t,by omega,hodd,heven,hstopBack,honesBack,hzeros,hbank,hcanonical,hreserve,hprefix,hbackcarry,
    segAdd machine _ _ _ n ksteps hfirst hsecond⟩

end Shared.Beeping.NPcoNP.NativeHalfEntryTo28

#print axioms Shared.Beeping.NPcoNP.NativeHalfEntryTo28.selected_entry_to28
