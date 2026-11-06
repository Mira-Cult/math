import Shared.Beeping.NPcoNP.NativeFirstZeroOperation

/-! Literal state-72 zero preparation for a finite, nonempty zero run followed
by a one. This local theorem records exact tape changes and finite silent
time; it does not assume that the layout is reachable. -/
namespace Shared.Beeping.NPcoNP.Native72Prepare
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerReturns
open Shared.Beeping.NPcoNP.NativeFirstZeroOperation
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

theorem step72_zero (x : Int) (t : Int → Bool) (ht : t x=false) :
    machine.step (cfg 72 x t)=(cfg 9 (x+1) (setAt x t),false) := by
  have row : machine.table.row 72 false=⟨true,.right,9,false⟩ := by decide
  have hw : (⟨72,x,t⟩ : Config 284).write true=setAt x t := rfl
  simp [cfg,Machine.step,ht,row,Move.apply,hw]

/-- State 72 writes its preparation marker, crosses two zeros, fills the
specified nonempty zero run and returns to state 83. Its full tape effect and
every disjoint tape cell are recorded. -/
theorem zero_prepare_to83 (x : Int) (t : Int → Bool) (k : Nat)
    (hk : 0<k)
    (h0 : t x=false) (h1 : t (x+1)=false) (h2 : t (x+2)=false)
    (zeros : ∀ i : Nat, i<k → t (x+3+(i : Int))=false)
    (marker : t (x+3+(k : Int))=true) :
    let out := fillRange (setAt x t) (x+3) (x+3+(k : Int))
    out x=true ∧
    (∀ q, q≠x → (q<x+3 ∨ x+3+(k : Int)≤q) → out q=t q) ∧
    silentSegment machine (cfg 72 x t) (cfg 83 (x+3+(k : Int)-2) out) (k+5) := by
  dsimp only
  let u := setAt x t
  have h1' : u (x+1)=false := by simp [u,setAt,show x+1≠x by omega,h1]
  have h2' : u (x+2)=false := by simp [u,setAt,show x+2≠x by omega,h2]
  have a := oneSeg machine _ _ (step72_zero x t h0)
  have b := oneSeg machine _ _ (step9_zero (x+1) u h1')
  have c := oneSeg machine _ _ (step42_zero (x+2) u h2')
  have ab : silentSegment machine (cfg 72 x t) (cfg 42 (x+2) u) 2 := by
    have hh := segAdd machine _ _ _ 1 1 a b
    simpa [u,Int.add_assoc] using hh
  have abc : silentSegment machine (cfg 72 x t) (cfg 10 (x+3) u) 3 := by
    have hh := segAdd machine _ _ _ 2 1 ab c
    simpa [Int.add_assoc] using hh
  have hz : ∀ i : Nat, i<k → u (x+3+(i : Int))=false := by
    intro i hi
    simp only [u,setAt,if_neg (show x+3+(i : Int)≠x by omega)]
    exact zeros i hi
  have hm : u (x+3+(k : Int))=true := by
    simp only [u,setAt,if_neg (show x+3+(k : Int)≠x by omega)]
    exact marker
  have hscan := scan10_return83 k (x+3) u hk hz hm
  have hall := segAdd machine _ _ _ 3 (k+2) abc hscan
  refine ⟨?_,?_,?_⟩
  · simp [fillRange,setAt]
  · intro q hne hside
    have hn : ¬ (x+3≤q ∧ q<x+3+(k : Int)) := by rcases hside with h | h <;> omega
    simp [fillRange,setAt,hn,hne]
  · have ht : 3+(k+2)=k+5 := by omega
    simpa only [u,ht] using hall

#print axioms zero_prepare_to83
end Shared.Beeping.NPcoNP.Native72Prepare
