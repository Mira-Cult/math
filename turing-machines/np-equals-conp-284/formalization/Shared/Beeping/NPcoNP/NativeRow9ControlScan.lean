import Shared.Beeping.NPcoNP.NativeZeroRestore

/-! Literal control transitions and forward scan for the row-9 increment.
The tape windows in these lemmas are supplied, not reachability assertions. -/
namespace Shared.Beeping.NPcoNP.NativeRow9ControlScan
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem step264_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 264 h t)=(cfg 44 (h+1) t,false) := by
  have row : machine.table.row 264 false=⟨false,.right,44,false⟩ := by decide
  have hw : (⟨264,h,t⟩ : Config 284).write false=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row,Move.apply,hw]

theorem step44_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 44 h t)=(cfg 29 (h+1) t,false) := by
  have row : machine.table.row 44 false=⟨false,.right,29,false⟩ := by decide
  have hw : (⟨44,h,t⟩ : Config 284).write false=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row,Move.apply,hw]

theorem step29_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 29 h t)=(cfg 265 (h+1) (setAt h t),false) := by
  have row : machine.table.row 29 false=⟨true,.right,265,false⟩ := by decide
  have hw : (⟨29,h,t⟩ : Config 284).write true=setAt h t := rfl
  simp [cfg,Machine.step,ht,row,Move.apply,hw]

theorem step265_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 265 h t)=(cfg 266 (h+1) t,false) := by
  have row : machine.table.row 265 false=⟨false,.right,266,false⟩ := by decide
  have hw : (⟨265,h,t⟩ : Config 284).write false=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row,Move.apply,hw]

theorem step265_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 265 h t)=(cfg 265 (h+1) t,false) := by
  have row : machine.table.row 265 true=⟨true,.right,265,false⟩ := by decide
  have hw : (⟨265,h,t⟩ : Config 284).write true=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row,Move.apply,hw]

theorem step266_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 266 h t)=(cfg 265 (h+1) t,false) := by
  have row : machine.table.row 266 true=⟨true,.right,265,false⟩ := by decide
  have hw : (⟨266,h,t⟩ : Config 284).write true=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row,Move.apply,hw]

theorem step266_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 266 h t)=(cfg 14 (h+1) (setAt h t),false) := by
  have row : machine.table.row 266 false=⟨true,.right,14,false⟩ := by decide
  have hw : (⟨266,h,t⟩ : Config 284).write true=setAt h t := rfl
  simp [cfg,Machine.step,ht,row,Move.apply,hw]

/-- Scan a prefix with no adjacent zeros, restore the second terminal zero,
then enter state 14. The complete tape and exact duration are given. -/
theorem scan265 (xs : List Bool) (hx : Prefix xs) (h : Int) (t : Int → Bool)
    (hm : Holds t h (xs ++ [false,false])) :
    silentSegment machine (cfg 265 h t)
      (cfg 14 (h+(xs.length : Int)+2) (setAt (h+(xs.length : Int)+1) t)) (xs.length+2) := by
  induction hx generalizing h with
  | nil =>
    simp only [List.nil_append,downHolds,Holds] at hm
    have a := oneSeg machine _ _ (step265_zero h t hm.1)
    have b := oneSeg machine _ _ (step266_zero (h+1) t hm.2.1)
    have all := segAdd machine _ _ _ 1 1 a b
    have he : h+1+1=h+2 := by omega
    simpa [he] using all
  | @one xs hx ih =>
    simp only [List.cons_append,Holds] at hm
    have a := oneSeg machine _ _ (step265_one h t hm.1)
    have b := ih (h+1) hm.2
    have all := segAdd machine _ _ _ 1 (xs.length+2) a b
    simpa [Int.add_assoc,Int.add_comm,Int.add_left_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all
  | @zeroOne xs hx ih =>
    simp only [List.cons_append,Holds] at hm
    have a := oneSeg machine _ _ (step265_zero h t hm.1)
    have b := oneSeg machine _ _ (step266_one (h+1) t hm.2.1)
    have c := ih (h+1+1) hm.2.2
    have ab := segAdd machine _ _ _ 1 1 a b
    have all := segAdd machine _ _ _ 2 (xs.length+2) ab c
    have he : h+(((false::true::xs).length : Nat) : Int)+2 = h+1+1+(xs.length : Int)+2 := by simp; omega
    have hp : h+(((false::true::xs).length : Nat) : Int)+1 = h+1+1+(xs.length : Int)+1 := by simp; omega
    have hn : (false::true::xs).length+2=2+(xs.length+2) := by simp; omega
    rw [he,hp,hn]
    exact all

#print axioms scan265
#print axioms step264_zero
#print axioms step29_zero
end Shared.Beeping.NPcoNP.NativeRow9ControlScan
