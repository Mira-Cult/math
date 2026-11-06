import Shared.Beeping.NPcoNP.NativeHalfCleanupScan
import Shared.Beeping.NPcoNP.NativeHalfOddCleanupSweep

/-! Forward scan of the odd HALF cleanup: literal states 36/37 find the
next double zero, after which state 38 performs the proved reverse sweep. -/
namespace Shared.Beeping.NPcoNP.NativeHalfOddCleanupScan

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfCleanupScan
open Shared.Beeping.NPcoNP.UnarySuffixShift

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem row36_zero : machine.table.row 36 false = ⟨false,.right,37,false⟩ := by decide
theorem row36_one : machine.table.row 36 true = ⟨true,.right,36,false⟩ := by decide
theorem row37_zero : machine.table.row 37 false = ⟨false,.left,38,false⟩ := by decide
theorem row37_one : machine.table.row 37 true = ⟨true,.right,36,false⟩ := by decide

theorem step36_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 36 h t)=(cfg 37 (h+1) t,false) := by
  have hw : (⟨36,h,t⟩ : Config 284).write false=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row36_zero,Move.apply,hw]

theorem step36_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 36 h t)=(cfg 36 (h+1) t,false) := by
  have hw : (⟨36,h,t⟩ : Config 284).write true=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row36_one,Move.apply,hw]

theorem step37_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 37 h t)=(cfg 38 (h-1) t,false) := by
  have hw : (⟨37,h,t⟩ : Config 284).write false=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row37_zero,Move.apply,hw]

theorem step37_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 37 h t)=(cfg 36 (h+1) t,false) := by
  have hw : (⟨37,h,t⟩ : Config 284).write true=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row37_one,Move.apply,hw]

/-- Entering state 37 on the first one of a prepared prefix scans to the
first double zero, preserving the complete tape. -/
theorem scan37 (xs : List Bool) (hp : Prefix xs) (h : Int) (t : Int → Bool)
    (hm : Holds t h (true :: (xs ++ [false,false]))) :
    silentSegment machine (cfg 37 h t) (cfg 38 (h+1+xs.length) t) (xs.length+3) := by
  change t h=true ∧ Holds t (h+1) (xs ++ [false,false]) at hm
  have hfirst := oneSeg machine _ _ (step37_one h t hm.1)
  have hrest := scan machine 36 37 38 step36_one step36_zero step37_one step37_zero
    xs hp (h+1) t hm.2
  have h := segAdd machine _ _ _ 1 (xs.length+2) hfirst hrest
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem prefix_tail_of_zero {xs : List Bool} (h : Prefix (false :: xs)) : Prefix xs := by
  cases h with
  | zeroOne h => exact .one h

theorem prefix_tail_of_one {xs : List Bool} (h : Prefix (true :: xs)) : Prefix xs := by
  cases h with
  | one h => exact h

/-- The suffix starts with one even when the bank is empty: in that case
the freshly appended zero-valued reserve supplies the one. -/
theorem encoded_reserve_starts_one (values : List Nat) :
    ∃ xs : List Bool, UnaryBank.encode values ++ [true] = true :: xs := by
  cases values with
  | nil => exact ⟨[],rfl⟩
  | cons n ns =>
    refine ⟨List.replicate n true ++ [false] ++ UnaryBank.encode ns ++ [true],?_⟩
    simp [UnaryBank.encode,UnaryBank.block,List.replicate_succ,List.append_assoc]

/-- On the tape produced by the odd residual, the forward cleanup reaches
state 38 in positive finite time with an exact head and unchanged tape. -/
theorem scan37_after_zero_prefix (base : Int → Bool) (gap : Int) (values : List Nat) :
    let t := after base gap (false :: UnaryBank.encode values)
    let pre := UnaryBank.encode values ++ [true]
    silentSegment machine (cfg 37 (gap+2) t)
      (cfg 38 (gap+2+pre.length) t) (pre.length+2) := by
  dsimp only
  let t := after base gap (false :: UnaryBank.encode values)
  obtain ⟨xs,hxs⟩ := encoded_reserve_starts_one values
  have hp : Prefix (UnaryBank.encode values ++ [true]) :=
    prefix_tail_of_zero (prefix_zero_encoded values)
  rw [hxs] at hp
  have hp' := prefix_tail_of_one hp
  have hh := holds_after_suffix base gap (false :: UnaryBank.encode values)
  change Holds t (gap+1) ((false :: UnaryBank.encode values) ++ [true,false,false]) at hh
  simp only [List.cons_append,Holds] at hh
  have ht : Holds t (gap+2) ((UnaryBank.encode values ++ [true]) ++ [false,false]) := by
    simpa [Int.add_assoc,List.append_assoc] using hh.2
  rw [hxs] at ht
  have hs := scan37 xs hp' (gap+2) t ht
  have hlen : (UnaryBank.encode values ++ [true]).length=xs.length+1 := by rw [hxs]; simp
  rw [hlen]
  have hpos : gap+2+((xs.length+1 : Nat) : Int)=gap+2+1+(xs.length : Int) := by push_cast; omega
  rw [hpos]
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs

end Shared.Beeping.NPcoNP.NativeHalfOddCleanupScan

#print axioms Shared.Beeping.NPcoNP.NativeHalfOddCleanupScan.scan37_after_zero_prefix
