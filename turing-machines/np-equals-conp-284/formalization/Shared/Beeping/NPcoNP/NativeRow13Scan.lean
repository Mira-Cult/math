import Shared.Beeping.NPcoNP.NativeRow13Enter
import Shared.Beeping.NPcoNP.NativeFirstNextPath
import Shared.Beeping.NPcoNP.NativeHalfBankFirst

/-! The state-46/45 scan to the beginning of the row-13 unary bank. -/
namespace Shared.Beeping.NPcoNP.NativeRow13Scan
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeFirstNextPath
open Shared.Beeping.NPcoNP.NativeRow12Carry
open Shared.Beeping.NPcoNP.NativeRow13Enter
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

theorem step46_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 46 h t)=(cfg 45 (h+1) t,false) :=
  unchanged_right 46 45 false h t (by decide) ht

theorem step45_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 45 h t)=(cfg 45 (h+1) t,false) :=
  unchanged_right 45 45 true h t (by decide) ht

theorem step45_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 45 h t)=(cfg 44 (h+1) t,false) :=
  unchanged_right 45 44 false h t (by decide) ht

/-- Scan a supplied finite run of ones and its zero delimiter. -/
theorem scan45 (n : Nat) (h : Int) (t : Int → Bool)
    (ones : ∀ i : Nat, i<n → t (h+(i : Int))=true)
    (zero : t (h+(n : Int))=false) :
    silentSegment machine (cfg 45 h t) (cfg 44 (h+(n : Int)+1) t) (n+1) := by
  induction n generalizing h with
  | zero =>
    have hz : t h=false := by simpa using zero
    simpa using oneSeg machine _ _ (step45_zero h t hz)
  | succ n ih =>
    have ho : t h=true := by simpa using ones 0 (by omega)
    have hr : ∀ i : Nat, i<n → t ((h+1)+(i : Int))=true := by
      intro i hi
      have hh := ones (i+1) (by omega)
      simpa [Nat.cast_add,Int.add_assoc,Int.add_comm,Int.add_left_comm] using hh
    have hz : t ((h+1)+(n : Int))=false := by
      simpa [Nat.cast_add,Int.add_assoc,Int.add_comm,Int.add_left_comm] using zero
    have first := oneSeg machine _ _ (step45_one h t ho)
    have next := ih (h+1) hr hz
    have all := segAdd machine _ _ _ 1 (n+1) first next
    convert all using 1 <;> simp [Nat.cast_add,Int.add_assoc,Int.add_comm,Int.add_left_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- From the supplied long-gap path the physical machine reaches the first
bank cell in state 44, silently and without changing the data suffix. -/
theorem enter_bank (h separator : Int) (t : Int → Bool)
    (hlong : h+14≤separator) (path : Holds t (h-4) NativeRow12Carry.nextPath)
    (left : ∀ q, q<h-4 → t q=false)
    (gap : ∀ q, h+7<q → q<separator-1 → t q=false)
    (marker : t (separator-1)=true) (sep : t separator=false) :
    let u := fillRange (setAt (h+10) t) (h+12) (separator-1)
    let out := clearAt (h+10) u
    ∃ k : Nat, 0<k ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (h-3) t) (cfg 44 (separator+1) out) k := by
  dsimp only
  let u := fillRange (setAt (h+10) t) (h+12) (separator-1)
  let out := clearAt (h+10) u
  obtain ⟨k,hk,hframe,hseg⟩ := enter_scanner h separator t hlong path left gap marker
  have hz : out (h+11)=false := by
    have hh := gap (h+11) (by omega) (by omega)
    simpa [out,u,clearAt,fillRange,setAt] using hh
  let r := (separator-(h+12)).toNat
  have hr : (r : Int)=separator-(h+12) := Int.toNat_of_nonneg (by omega)
  have ho : ∀ i : Nat, i<r → out (h+12+(i : Int))=true := by
    intro i hi
    let q : Int := h+12+(i : Int)
    have hq : h+12≤q ∧ q<separator := by dsimp [q]; omega
    change out q=true
    by_cases he : q=separator-1
    · rw [he]
      have hn : ¬ (h+12≤separator-1 ∧ separator-1<separator-1) := by omega
      simpa [out,u,clearAt,fillRange,setAt,hn,show separator-1≠h+10 by omega] using marker
    · simp [out,u,clearAt,fillRange,hq.1,show q<separator-1 by omega,show q≠h+10 by omega]
  have hs : out (h+12+(r : Int))=false := by
    have he : h+12+(r : Int)=separator := by omega
    rw [he]
    exact (hframe separator (le_refl _)).trans sep
  have first := oneSeg machine _ _ (step46_zero (h+11) out hz)
  have first' : silentSegment machine (cfg 46 (h+11) out) (cfg 45 (h+12) out) 1 := by
    simpa only [show h+11+1=h+12 by omega] using first
  have next := scan45 r (h+12) out ho hs
  have next' : silentSegment machine (cfg 45 (h+12) out) (cfg 44 (separator+1) out) (r+1) := by
    have he : h+12+(r : Int)+1=separator+1 := by omega
    simpa only [he] using next
  exact ⟨k+1+(r+1),by omega,hframe,
    segAdd machine _ _ _ (k+1) (r+1) (segAdd machine _ _ _ k 1 hseg first') next'⟩

theorem step44_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 44 h t)=(cfg 44 (h+1) t,false) :=
  unchanged_right 44 44 true h t (by decide) ht

theorem step44_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 44 h t)=(cfg 29 (h+1) t,false) :=
  unchanged_right 44 29 false h t (by decide) ht

/-- Scan a supplied finite run of ones and its zero delimiter. -/
theorem scan44 (n : Nat) (h : Int) (t : Int → Bool)
    (ones : ∀ i : Nat, i<n → t (h+(i : Int))=true)
    (zero : t (h+(n : Int))=false) :
    silentSegment machine (cfg 44 h t) (cfg 29 (h+(n : Int)+1) t) (n+1) := by
  induction n generalizing h with
  | zero =>
    have hz : t h=false := by simpa using zero
    simpa using oneSeg machine _ _ (step44_zero h t hz)
  | succ n ih =>
    have ho : t h=true := by simpa using ones 0 (by omega)
    have hr : ∀ i : Nat, i<n → t ((h+1)+(i : Int))=true := by
      intro i hi
      have hh := ones (i+1) (by omega)
      simpa [Nat.cast_add,Int.add_assoc,Int.add_comm,Int.add_left_comm] using hh
    have hz : t ((h+1)+(n : Int))=false := by
      simpa [Nat.cast_add,Int.add_assoc,Int.add_comm,Int.add_left_comm] using zero
    have first := oneSeg machine _ _ (step44_one h t ho)
    have next := ih (h+1) hr hz
    have all := segAdd machine _ _ _ 1 (n+1) first next
    convert all using 1 <;> simp [Nat.cast_add,Int.add_assoc,Int.add_comm,Int.add_left_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]


/-- The first unary block is traversed in full, and state 29 arrives at
its successor block. This proves no branch outcome for that second block. -/
theorem enter_selected (h separator : Int) (t : Int → Bool) (a : Nat) (rest : List Nat)
    (hlong : h+14≤separator) (path : Holds t (h-4) NativeRow12Carry.nextPath)
    (left : ∀ q, q<h-4 → t q=false)
    (gap : ∀ q, h+7<q → q<separator-1 → t q=false)
    (marker : t (separator-1)=true) (sep : t separator=false)
    (bank : Holds t (separator+1) (encode (a::rest))) :
    let u := fillRange (setAt (h+10) t) (h+12) (separator-1)
    let out := clearAt (h+10) u
    ∃ k : Nat, 0<k ∧ Holds out (separator+1+((a+2 : Nat):Int)) (encode rest) ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (h-3) t)
        (cfg 29 (separator+1+((a+2 : Nat):Int)) out) k := by
  dsimp only
  let u := fillRange (setAt (h+10) t) (h+12) (separator-1)
  let out := clearAt (h+10) u
  obtain ⟨k,hk,hframe,hseg⟩ := enter_bank h separator t hlong path left gap marker sep
  have hb : Holds out (separator+1) (encode (a::rest)) := by
    apply holds_transport t out _ _ bank
    intro q hq _
    exact (hframe q (by omega)).symm
  have cells := first_block_cells out (separator+1) a rest hb
  have next := scan44 (a+1) (separator+1) out (by intro i hi; exact cells.1 i (by omega)) cells.2
  have next' : silentSegment machine (cfg 44 (separator+1) out)
      (cfg 29 (separator+1+((a+2 : Nat):Int)) out) (a+2) := by
    have he : separator+1+((a+1 : Nat):Int)+1=separator+1+((a+2 : Nat):Int) := by push_cast; omega
    simpa only [he,show (a+1)+1=a+2 by omega] using next
  exact ⟨k+(a+2),by omega,first_block_tail out (separator+1) a rest hb,hframe,
    segAdd machine _ _ _ k (a+2) hseg next'⟩

#print axioms enter_selected
#print axioms scan44
#print axioms scan45
#print axioms enter_bank
end Shared.Beeping.NPcoNP.NativeRow13Scan
