import Shared.Beeping.NPcoNP.NativeHalfMarkerMany

/-! Literal state-15 branch following a selector value of at least three.
The finite words and delimiters are supplied; this is not an all-run invariant. -/
namespace Shared.Beeping.NPcoNP.NativeManySelectorReturn
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem row15_one : machine.table.row 15 true = ⟨true,.right,15,false⟩ := by decide
theorem row15_zero : machine.table.row 15 false = ⟨false,.right,11,false⟩ := by decide
theorem row11_one : machine.table.row 11 true = ⟨true,.right,11,false⟩ := by decide
theorem row11_zero : machine.table.row 11 false = ⟨false,.right,13,false⟩ := by decide

theorem step15_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 15 h t)=(cfg 15 (h+1) t,false) := by
  have hw : (⟨15,h,t⟩ : Config 284).write true=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row15_one,Move.apply,hw]
theorem step15_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 15 h t)=(cfg 11 (h+1) t,false) := by
  have hw : (⟨15,h,t⟩ : Config 284).write false=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row15_zero,Move.apply,hw]
theorem step11_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 11 h t)=(cfg 11 (h+1) t,false) := by
  have hw : (⟨11,h,t⟩ : Config 284).write true=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row11_one,Move.apply,hw]
theorem step11_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 11 h t)=(cfg 13 (h+1) t,false) := by
  have hw : (⟨11,h,t⟩ : Config 284).write false=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row11_zero,Move.apply,hw]

/-- A supplied finite run of ones and zero delimiter is scanned without writes. -/
theorem scan15 (n : Nat) (h : Int) (t : Int → Bool)
    (ht : Holds t h (List.replicate n true ++ [false])) :
    silentSegment machine (cfg 15 h t) (cfg 11 (h+n+1) t) (n+1) := by
  induction n generalizing h with
  | zero =>
    simp only [List.replicate_zero,List.nil_append,Holds] at ht
    simpa using oneSeg machine _ _ (step15_zero h t ht.1)
  | succ n ih =>
    simp only [List.replicate_succ,List.cons_append,Holds] at ht
    have hs := oneSeg machine _ _ (step15_one h t ht.1)
    have hr := ih (h+1) ht.2
    have hall := segAdd machine _ _ _ 1 (n+1) hs hr
    simpa [Int.add_assoc,Int.add_comm,Int.add_left_comm,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using hall

theorem scan11 (n : Nat) (h : Int) (t : Int → Bool)
    (ht : Holds t h (List.replicate n true ++ [false])) :
    silentSegment machine (cfg 11 h t) (cfg 13 (h+n+1) t) (n+1) := by
  induction n generalizing h with
  | zero =>
    simp only [List.replicate_zero,List.nil_append,Holds] at ht
    simpa using oneSeg machine _ _ (step11_zero h t ht.1)
  | succ n ih =>
    simp only [List.replicate_succ,List.cons_append,Holds] at ht
    have hs := oneSeg machine _ _ (step11_one h t ht.1)
    have hr := ih (h+1) ht.2
    have hall := segAdd machine _ _ _ 1 (n+1) hs hr
    simpa [Int.add_assoc,Int.add_comm,Int.add_left_comm,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using hall

#print axioms scan15
#print axioms scan11
end Shared.Beeping.NPcoNP.NativeManySelectorReturn
