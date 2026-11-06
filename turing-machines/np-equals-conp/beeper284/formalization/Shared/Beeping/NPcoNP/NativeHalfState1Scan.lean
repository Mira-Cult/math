import Shared.Beeping.NPcoNP.NativeHalfSweep

/-! The literal 284-state table's state-1 leftward carry scan.
The input is an explicitly supplied finite run of ones followed by a zero.
This is a prepared tape segment, not a blank-start reachability theorem. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Shared.Beeping.NPcoNP.NativeHalfState1Scan

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep

theorem row1_one : machine.table.row 1 true = ⟨false, .left, 1, false⟩ := by decide
theorem row1_zero : machine.table.row 1 false = ⟨true, .right, 27, false⟩ := by decide

theorem step_one (h : Int) (t : Int → Bool) (ht : t h = true) :
    machine.step (cfg 1 h t) = (cfg 1 (h-1) (put t h false), false) := by
  change machine.step ⟨1,h,t⟩ = (⟨1,h-1,put t h false⟩,false)
  have hw : (⟨1,h,t⟩ : Config 284).write false = put t h false := rfl
  simp [Machine.step, ht, row1_one, Move.apply, hw]

theorem step_zero (h : Int) (t : Int → Bool) (ht : t h = false) :
    machine.step (cfg 1 h t) = (cfg 27 (h+1) (put t h true), false) := by
  change machine.step ⟨1,h,t⟩ = (⟨27,h+1,put t h true⟩,false)
  have hw : (⟨1,h,t⟩ : Config 284).write true = put t h true := rfl
  simp [Machine.step, ht, row1_zero, Move.apply, hw]

/-- Clear the finite interval strictly above `h-k` and at most `h`. -/
def cleared (t : Int → Bool) (h : Int) (k : Nat) : Int → Bool :=
  fun p => if h - (k : Int) < p ∧ p ≤ h then false else t p

theorem cleared_zero (t : Int → Bool) (h : Int) : cleared t h 0 = t := by
  funext p
  have hn : ¬ (h < p ∧ p ≤ h) := by omega
  simp [cleared, hn]

theorem cleared_succ (t : Int → Bool) (h : Int) (k : Nat) :
    cleared (put t h false) (h-1) k = cleared t h (k+1) := by
  funext p
  simp only [cleared, put, Nat.cast_add, Nat.cast_one]
  split_ifs <;> simp_all <;> omega

/-- Exactly `k` silent steps erase the asserted `k` consecutive ones. -/
theorem scan_ones (t : Int → Bool) (h : Int) (k : Nat)
    (hm : downHolds t h (List.replicate k true ++ [false])) :
    silentSegment machine (cfg 1 h t) (cfg 1 (h-(k : Int)) (cleared t h k)) k := by
  induction k generalizing t h with
  | zero =>
    simp [silentSegment, WordEventSystem.advance, WordEventSystem.wordFrom, cleared_zero]
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, downHolds] at hm
    have first := oneSeg machine _ _ (step_one h t hm.1)
    have htail : downHolds (put t h false) (h-1) (List.replicate k true ++ [false]) :=
      downHolds_put t (h-1) h _ false (by omega) hm.2
    have rest := ih (put t h false) (h-1) htail
    have joined := segAdd machine _ _ _ 1 k first rest
    have hc : cleared (put t h false) (h-1) k = cleared t h (k+1) := cleared_succ t h k
    have hp : h - 1 - (k : Int) = h - ((k+1 : Nat) : Int) := by omega
    simpa [hc, hp, Nat.add_comm] using joined

/-- Exact whole-tape effect: clear the ones and replace the first zero by one. -/
def result (t : Int → Bool) (h : Int) (k : Nat) : Int → Bool :=
  put (cleared t h k) (h-(k : Int)) true

theorem scan (t : Int → Bool) (h : Int) (k : Nat)
    (hm : downHolds t h (List.replicate k true ++ [false])) :
    silentSegment machine (cfg 1 h t)
      (cfg 27 (h-(k : Int)+1) (result t h k)) (k+1) := by
  have hzero : t (h-(k : Int)) = false := by
    induction k generalizing h with
    | zero => simpa [downHolds] using hm.1
    | succ k ih =>
      simp only [List.replicate_succ, List.cons_append, downHolds] at hm
      have hp : h - ((k+1 : Nat) : Int) = h - 1 - (k : Int) := by omega
      rw [hp]
      exact ih (h-1) hm.2
  have hfirst := scan_ones t h k hm
  have hread : cleared t h k (h-(k : Int)) = false := by
    simp [cleared, hzero]
  have hlast := oneSeg machine _ _ (step_zero (h-(k : Int)) (cleared t h k) hread)
  exact segAdd machine _ _ _ k 1 hfirst hlast

theorem scan_positive (k : Nat) : 0 < k+1 := by omega

theorem scan_no_beep (t : Int → Bool) (h : Int) (k j : Nat)
    (hm : downHolds t h (List.replicate k true ++ [false])) (hj : j < k+1) :
    ¬ machine.system.BeepFrom (cfg 1 h t) j :=
  silent_no_beep machine _ _ _ j (scan t h k hm) hj

end Shared.Beeping.NPcoNP.NativeHalfState1Scan
