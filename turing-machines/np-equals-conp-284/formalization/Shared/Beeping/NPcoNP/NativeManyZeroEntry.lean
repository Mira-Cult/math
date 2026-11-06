import Shared.Beeping.NPcoNP.NativeManyShift
import Shared.Beeping.NPcoNP.NativeHalfOddReturn
import Shared.Beeping.NPcoNP.NativeHalfState95Stop

/-! Zero-valued following-bank branch of the literal many-selector path.
A supplied finite left delimiter is required for the return to finish. -/
namespace Shared.Beeping.NPcoNP.NativeManyZeroEntry
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfOddReturn
open Shared.Beeping.NPcoNP.NativeHalfState95Stop
open Shared.Beeping.NPcoNP.NativeManyShift
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

theorem row13_zero : machine.table.row 13 false = ⟨true,.left,25,false⟩ := by decide
theorem row17_zero : machine.table.row 17 false = ⟨false,.left,13,false⟩ := by decide

theorem step13_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 13 h t)=(cfg 25 (h-1) (setAt h t),false) := by
  have hw : (⟨13,h,t⟩ : Config 284).write true=setAt h t := rfl
  simp [cfg,Machine.step,ht,row13_zero,Move.apply,hw]

theorem step17_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 17 h t)=(cfg 13 (h-1) t,false) := by
  have hw : (⟨17,h,t⟩ : Config 284).write false=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row17_zero,Move.apply,hw]

/-- A zero-valued unary block takes the failure return in exactly three
silent transitions; the temporary write is restored on the entire tape. -/
theorem zero_to25 (x : Int) (t : Int → Bool)
    (h0 : t x=true) (h1 : t (x+1)=false) :
    silentSegment machine (cfg 13 x t) (cfg 25 (x-1) t) 3 := by
  let u := clearAt x t
  have h1' : u (x+1)=false := by simp [u,clearAt,show x+1≠x by omega,h1]
  have h0' : u x=false := by simp [u,clearAt]
  have heq : setAt x u=t := by
    funext p
    by_cases hp : p=x
    · subst p; simp [u,setAt,clearAt,h0]
    · simp [u,setAt,clearAt,hp]
  have s1 := oneSeg machine _ _ (step13_1 x t h0)
  have s2 := oneSeg machine _ _ (step17_zero (x+1) u h1')
  have s3 := oneSeg machine _ _ (step13_zero x u h0')
  have s12 := segAdd machine _ _ _ 1 1 s1 s2
  have s12' : silentSegment machine (cfg 13 x t) (cfg 13 x u) 2 := by
    simpa only [show x+1-1=x by omega,u] using s12
  have hall := segAdd machine _ _ _ 2 1 s12' s3
  simpa only [heq] using hall

/-- The zero branch returns through states 25/26 and 95 to state 1,
provided both the finite double-zero boundary and the later state-95 zero
are explicitly supplied. Its exact output tape and finite bound are given. -/
theorem zero_to1 (x : Int) (t : Int → Bool) (s : Shape) (k : Nat)
    (h0 : t x=true) (h1 : t (x+1)=false)
    (hprefix : downHolds t (x-1) (bits s ++ [false,false]))
    (stop : t (x-1-(bits s).length-2-(k : Int))=false) :
    let pos := x-1-(bits s).length-2
    ∃ n : Nat, 0<n ∧ n≤k+1 ∧
      let out := clearRange t (pos-(n : Int)+2) (pos+1)
      (∀ z, pos+1≤z → out z=t z) ∧
      silentSegment machine (cfg 13 x t) (cfg 1 (pos-(n : Int)) out)
        (3+((bits s).length+2)+n) := by
  dsimp only
  let pos := x-1-(bits s).length-2
  have h25 := return_scan25 s (x-1) t hprefix
  have h25' : silentSegment machine (cfg 25 (x-1) t) (cfg 95 pos t)
      ((bits s).length+2) := by simpa [pos] using h25
  obtain ⟨n,hn,hbound,_hstop,_hones,h95⟩ := scan95_exact_with_stop k pos t stop
  let out := clearRange t (pos-(n : Int)+2) (pos+1)
  have hframe : ∀ z, pos+1≤z → out z=t z := by
    intro z hz
    have hn' : ¬ (pos-(n : Int)+2≤z ∧ z<pos+1) := by omega
    change (if pos-(n : Int)+2≤z ∧ z<pos+1 then false else t z)=t z
    rw [if_neg hn']
  have hfirst := zero_to25 x t h0 h1
  have hpre := segAdd machine _ _ _ 3 ((bits s).length+2) hfirst h25'
  refine ⟨n,hn,hbound,hframe,?_⟩
  exact segAdd machine _ _ _ (3+((bits s).length+2)) n hpre h95

#print axioms zero_to25
#print axioms zero_to1
end Shared.Beeping.NPcoNP.NativeManyZeroEntry
