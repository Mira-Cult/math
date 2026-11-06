import Shared.Beeping.NPcoNP.NativeAllBankPrepareReturn
import Shared.Beeping.NPcoNP.NativeHalfScannerReturns
import Shared.Beeping.NPcoNP.NativeHalfState97Progress

/-! Zero-entry preparation shared by literal HALF entry states 74--77.
The HALF bank operation itself is a separate obligation. -/
namespace Shared.Beeping.NPcoNP.NativeHalfZeroPreparation
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState97Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerReturns
open Shared.Beeping.NPcoNP.NativeSelectorThirteen
open Shared.Beeping.NPcoNP.NativeIncBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

theorem half_zero_row (q : Fin 284) (hq : q=74 ∨ q=75 ∨ q=76 ∨ q=77) :
    machine.table.row q false=⟨true,.right,42,false⟩ := by
  rcases hq with rfl | rfl | rfl | rfl <;> decide

theorem half_zero_step (q : Fin 284) (hq : q=74 ∨ q=75 ∨ q=76 ∨ q=77)
    (x : Int) (t : Int → Bool) (h0 : t x=false) :
    machine.step (cfg q x t)=(cfg 42 (x+1) (setAt x t),false) := by
  have hw : (⟨q,x,t⟩ : Config 284).write true=setAt x t := rfl
  simp [cfg,Machine.step,h0,half_zero_row q hq,Move.apply,hw]

theorem zero_prepare_to83 (q : Fin 284) (hq : q=74 ∨ q=75 ∨ q=76 ∨ q=77)
    (x : Int) (t : Int → Bool) (k : Nat) (h0 : t x=false) (h1 : t (x+1)=false)
    (zeros : ∀ i : Nat, i<k → t (x+2+(i : Int))=false)
    (marker : t (x+2+(k : Int))=true) :
    let out := fillRange (setAt x t) (x+2) (x+2+(k : Int))
    let head := if k=0 then x-1 else x+2+(k : Int)-2
    let duration := if k=0 then 5 else k+4
    silentSegment machine (cfg q x t) (cfg 83 head out) duration := by
  dsimp only
  let u := setAt x t
  have hu1 : u (x+1)=false := by simp [u,setAt,show x+1≠x by omega,h1]
  have a := oneSeg machine _ _ (half_zero_step q hq x t h0)
  have b := oneSeg machine _ _ (step42_zero (x+1) u hu1)
  have ab : silentSegment machine (cfg q x t) (cfg 10 (x+2) u) 2 := by
    simpa [u,Int.add_assoc] using segAdd machine _ _ _ 1 1 a b
  cases k with
  | zero =>
    have hu2 : u (x+2)=true := by simpa [u,setAt,show x+2≠x by omega] using marker
    have hu0 : u x=true := by simp [u,setAt]
    have c := oneSeg machine _ _ (step10_one (x+2) u hu2)
    have c' : silentSegment machine (cfg 10 (x+2) u) (cfg 97 (x+1) u) 1 := by
      simpa only [show x+2-1=x+1 by omega] using c
    have d := oneSeg machine _ _ (step97_zero (x+1) u hu1)
    have d' : silentSegment machine (cfg 97 (x+1) u) (cfg 97 x u) 1 := by simpa using d
    have e := oneSeg machine _ _ (step97_one x u hu0)
    have abc := segAdd machine _ _ _ 2 1 ab c'
    have abcd := segAdd machine _ _ _ 3 1 abc d'
    have all := segAdd machine _ _ _ 4 1 abcd e
    simpa [u,fill_empty] using all
  | succ k =>
    have hz : ∀ i : Nat, i<k+1 → u (x+2+(i : Int))=false := by
      intro i hi
      simp only [u,setAt,if_neg (show x+2+(i : Int)≠x by omega)]
      exact zeros i hi
    have hm : u (x+2+((k+1 : Nat) : Int))=true := by
      change (if x+2+((k+1 : Nat) : Int)=x then true else t (x+2+((k+1 : Nat) : Int)))=true
      rw [if_neg (by omega)]
      simpa using marker
    have hscan := scan10_return83 (k+1) (x+2) u (by omega) hz hm
    have all := segAdd machine _ _ _ 2 ((k+1)+2) ab hscan
    simpa [u,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all

#print axioms zero_prepare_to83
end Shared.Beeping.NPcoNP.NativeHalfZeroPreparation
