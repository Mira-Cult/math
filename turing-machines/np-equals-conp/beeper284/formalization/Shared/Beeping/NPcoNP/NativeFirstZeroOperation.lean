import Shared.Beeping.NPcoNP.NativeFirstDispatch
import Shared.Beeping.NPcoNP.NativeHalfScannerReturns

/-! The literal zero branch after state 166. The finite zero run and its
terminating one are explicit premises; this does not claim reachability or
identify the resulting graph program counter. -/
namespace Shared.Beeping.NPcoNP.NativeFirstZeroOperation
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerReturns
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

theorem row166_zero : machine.table.row 166 false = ⟨false,.right,100,false⟩ := by decide
theorem row100_zero : machine.table.row 100 false = ⟨false,.right,62,false⟩ := by decide
theorem row62_zero : machine.table.row 62 false = ⟨true,.right,9,false⟩ := by decide
theorem row9_zero : machine.table.row 9 false = ⟨false,.right,42,false⟩ := by decide

theorem step166_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 166 h t)=(cfg 100 (h+1) t,false) := by
  have hw : (⟨166,h,t⟩ : Config 284).write false=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row166_zero,Move.apply,hw]

theorem step100_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 100 h t)=(cfg 62 (h+1) t,false) := by
  have hw : (⟨100,h,t⟩ : Config 284).write false=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row100_zero,Move.apply,hw]

theorem step62_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 62 h t)=(cfg 9 (h+1) (setAt h t),false) := by
  have hw : (⟨62,h,t⟩ : Config 284).write true=setAt h t := rfl
  simp [cfg,Machine.step,ht,row62_zero,Move.apply,hw]

theorem step9_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 9 h t)=(cfg 42 (h+1) t,false) := by
  have hw : (⟨9,h,t⟩ : Config 284).write false=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row9_zero,Move.apply,hw]

/-- The five zero-branch rows pay for every step and only set cell `h+2`. -/
theorem zero_to10 (h : Int) (t : Int → Bool)
    (h0 : t h=false) (h1 : t (h+1)=false) (h2 : t (h+2)=false)
    (h3 : t (h+3)=false) (h4 : t (h+4)=false) :
    silentSegment machine (cfg 166 h t) (cfg 10 (h+5) (setAt (h+2) t)) 5 := by
  let u := setAt (h+2) t
  have h3' : u (h+3)=false := by simp [u,setAt,show h+3≠h+2 by omega,h3]
  have h4' : u (h+4)=false := by simp [u,setAt,show h+4≠h+2 by omega,h4]
  have a := oneSeg machine _ _ (step166_zero h t h0)
  have b := oneSeg machine _ _ (step100_zero (h+1) t h1)
  have c := oneSeg machine _ _ (step62_zero (h+2) t h2)
  have d := oneSeg machine _ _ (step9_zero (h+3) u h3')
  have e := oneSeg machine _ _ (step42_zero (h+4) u h4')
  have ab : silentSegment machine (cfg 166 h t) (cfg 62 (h+2) t) 2 := by
    have hh := segAdd machine _ _ _ 1 1 a b
    simpa [Int.add_assoc] using hh
  have abc : silentSegment machine (cfg 166 h t) (cfg 9 (h+3) u) 3 := by
    have hh := segAdd machine _ _ _ 2 1 ab c
    simpa [u,Int.add_assoc] using hh
  have abcd : silentSegment machine (cfg 166 h t) (cfg 42 (h+4) u) 4 := by
    have hh := segAdd machine _ _ _ 3 1 abc d
    simpa [Int.add_assoc] using hh
  have all := segAdd machine _ _ _ 4 1 abcd e
  simpa [u,Int.add_assoc] using all

/-- A supplied nonempty zero run ending in one forces a finite silent return.
The whole output tape, time, head and suffix frame are explicit. -/
theorem zero_to83 (h : Int) (t : Int → Bool) (k : Nat)
    (hk : 0<k)
    (hprefix : ∀ i : Nat, i<5 → t (h+(i : Int))=false)
    (zeros : ∀ i : Nat, i<k → t (h+5+(i : Int))=false)
    (marker : t (h+5+(k : Int))=true) :
    let out := fillRange (setAt (h+2) t) (h+5) (h+5+(k : Int))
    (∀ q, h+5+(k : Int)≤q → out q=t q) ∧
    silentSegment machine (cfg 166 h t) (cfg 83 (h+5+(k : Int)-2) out) (k+7) := by
  dsimp only
  let u := setAt (h+2) t
  have h0 : t h=false := by simpa using hprefix 0 (by omega)
  have h1 : t (h+1)=false := by simpa using hprefix 1 (by omega)
  have h2 : t (h+2)=false := by simpa using hprefix 2 (by omega)
  have h3 : t (h+3)=false := by simpa using hprefix 3 (by omega)
  have h4 : t (h+4)=false := by simpa using hprefix 4 (by omega)
  have hz : ∀ i : Nat, i<k → u (h+5+(i : Int))=false := by
    intro i hi
    simp only [u,setAt,if_neg (show h+5+(i : Int)≠h+2 by omega)]
    exact zeros i hi
  have hm : u (h+5+(k : Int))=true := by
    simp only [u,setAt,if_neg (show h+5+(k : Int)≠h+2 by omega)]
    exact marker
  constructor
  · intro q hq
    have hf : ¬ (h+5≤q ∧ q<h+5+(k : Int)) := by omega
    have hs : q≠h+2 := by omega
    simp [fillRange,setAt,hf,hs]
  · have hs := segAdd machine _ _ _ 5 (k+2) (zero_to10 h t h0 h1 h2 h3 h4)
      (scan10_return83 k (h+5) u hk hz hm)
    simpa [u,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs

#print axioms zero_to10
#print axioms zero_to83
end Shared.Beeping.NPcoNP.NativeFirstZeroOperation
