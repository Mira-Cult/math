import Shared.Beeping.NPcoNP.Native50Prepare
import Shared.Beeping.NPcoNP.NativeBankRoundtrip
import Shared.Beeping.NPcoNP.NativeHalfSelectorReturn

/-! State 51 has the same zero preparation row as state 50. This is a
local tape theorem, not reachability or a complete graph-step simulation. -/
namespace Shared.Beeping.NPcoNP.Native51Prepare
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.Native50Prepare
open Shared.Beeping.NPcoNP.NativeBankRoundtrip
open Shared.Beeping.NPcoNP.NativeFirstZeroOperation
open Shared.Beeping.NPcoNP.NativeHalfState10Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.NativeHalfState97Progress
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

theorem step51_zero (x : Int) (t : Int → Bool) (ht : t x=false) :
    machine.step (cfg 51 x t)=(cfg 9 (x+1) (setAt x t),false) := by
  have row : machine.table.row 51 false=⟨true,.right,9,false⟩ := by decide
  have hw : (⟨51,x,t⟩ : Config 284).write true=setAt x t := rfl
  simp [cfg,Machine.step,ht,row,Move.apply,hw]

/-- A nonempty zero gap followed by a one makes the physical row-9
preparation finish silently; the exact tape and positive cost are explicit. -/
theorem zero_prepare_to83 (x : Int) (t : Int → Bool) (k : Nat)
    (hk : 0<k) (h0 : t x=false) (h1 : t (x+1)=false) (h2 : t (x+2)=false)
    (zeros : ∀ i : Nat, i<k → t (x+3+(i : Int))=false)
    (marker : t (x+3+(k : Int))=true) :
    let out := fillRange (setAt x t) (x+3) (x+3+(k : Int))
    out x=true ∧ (∀ q, q≠x → (q<x+3 ∨ x+3+(k : Int)≤q) → out q=t q) ∧
    silentSegment machine (cfg 51 x t) (cfg 83 (x+3+(k : Int)-2) out) (k+5) := by
  dsimp only
  let out := fillRange (setAt x t) (x+3) (x+3+(k : Int))
  obtain ⟨hm,hframe,h50⟩ := Native50Prepare.zero_prepare_to83 x t k hk h0 h1 h2 zeros marker
  have htail := silent_tail machine (cfg 50 x t) (cfg 9 (x+1) (setAt x t))
    (cfg 83 (x+3+(k : Int)-2) out) (k+4) (step50_zero x t h0) (by simpa using h50)
  have hfirst := oneSeg machine _ _ (step51_zero x t h0)
  have hall := segAdd machine _ _ _ 1 (k+4) hfirst htail
  exact ⟨hm,hframe,by simpa [out,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hall⟩

/-- The boundary case with the first one immediately after state 42's
zero cell costs seven steps and returns at the other side of the new marker. -/
theorem zero_prepare_empty_exact (x : Int) (t : Int → Bool)
    (h0 : t x=false) (h1 : t (x+1)=false) (h2 : t (x+2)=false)
    (marker : t (x+3)=true) :
    silentSegment machine (cfg 51 x t) (cfg 83 (x-1) (setAt x t)) 7 := by
  let u := setAt x t
  have hu1 : u (x+1)=false := by simp [u,setAt,show x+1≠x by omega,h1]
  have hu2 : u (x+2)=false := by simp [u,setAt,show x+2≠x by omega,h2]
  have hu3 : u (x+3)=true := by simp [u,setAt,show x+3≠x by omega,marker]
  have hu0 : u x=true := by simp [u,setAt]
  have a := oneSeg machine _ _ (step51_zero x t h0)
  have b := oneSeg machine _ _ (step9_zero (x+1) u hu1)
  have c := oneSeg machine _ _ (step42_zero (x+2) u hu2)
  have d := oneSeg machine _ _ (step10_one (x+3) u hu3)
  have e := oneSeg machine _ _ (step97_zero (x+2) u hu2)
  have f := oneSeg machine _ _ (step97_zero (x+1) u hu1)
  have g := oneSeg machine _ _ (step97_one x u hu0)
  have ab := segAdd machine _ _ _ 1 1 a b
  have abc := segAdd machine _ _ _ 2 1 (by simpa [Int.add_assoc] using ab) c
  have abcd := segAdd machine _ _ _ 3 1 (by simpa [Int.add_assoc] using abc) d
  have abcd' : silentSegment machine (cfg 51 x t) (cfg 97 (x+2) u) 4 := by
    simpa only [show x+3-1=x+2 by omega] using abcd
  have abcde := segAdd machine _ _ _ 4 1 abcd' e
  have abcde' : silentSegment machine (cfg 51 x t) (cfg 97 (x+1) u) 5 := by
    simpa only [show x+2-1=x+1 by omega] using abcde
  have abcdef := segAdd machine _ _ _ 5 1 abcde' f
  have abcdef' : silentSegment machine (cfg 51 x t) (cfg 97 x u) 6 := by
    simpa only [show x+1-1=x by omega] using abcdef
  exact segAdd machine _ _ _ 6 1 abcdef' g

/-- Uniform exact timing and returned head, including the empty gap. -/
theorem zero_prepare_to83_exact (x : Int) (t : Int → Bool) (k : Nat)
    (h0 : t x=false) (h1 : t (x+1)=false) (h2 : t (x+2)=false)
    (zeros : ∀ i : Nat, i<k → t (x+3+(i : Int))=false)
    (marker : t (x+3+(k : Int))=true) :
    let out := fillRange (setAt x t) (x+3) (x+3+(k : Int))
    let head := if k=0 then x-1 else x+3+(k : Int)-2
    let duration := if k=0 then 7 else k+5
    silentSegment machine (cfg 51 x t) (cfg 83 head out) duration := by
  cases k with
  | zero =>
    simpa [fill_empty] using zero_prepare_empty_exact x t h0 h1 h2 (by simpa using marker)
  | succ k =>
    obtain ⟨_,_,hs⟩ := zero_prepare_to83 x t (k+1) (by omega) h0 h1 h2 zeros marker
    simpa using hs

/-- Both empty and nonempty gaps finish the literal preparation silently.
The empty case may return to a different head, so its head is existential. -/
theorem zero_prepare_to83_all (x : Int) (t : Int → Bool) (k : Nat)
    (h0 : t x=false) (h1 : t (x+1)=false) (h2 : t (x+2)=false)
    (zeros : ∀ i : Nat, i<k → t (x+3+(i : Int))=false)
    (marker : t (x+3+(k : Int))=true) :
    let out := fillRange (setAt x t) (x+3) (x+3+(k : Int))
    ∃ (n : Nat) (head : Int), 0<n ∧
      silentSegment machine (cfg 51 x t) (cfg 83 head out) n := by
  have hs := zero_prepare_to83_exact x t k h0 h1 h2 zeros marker
  refine ⟨if k=0 then 7 else k+5, if k=0 then x-1 else x+3+(k:Int)-2, ?_, hs⟩
  split_ifs <;> omega

#print axioms step51_zero
#print axioms zero_prepare_to83
#print axioms zero_prepare_to83_all
#print axioms zero_prepare_empty_exact
#print axioms zero_prepare_to83_exact
end Shared.Beeping.NPcoNP.Native51Prepare
