import Shared.Beeping.NPcoNP.NativeHalfSweep

/-! A prepared leftward return scan of the literal 284-state table. States
23 and 24 leave the entire tape unchanged while searching for a double zero.
The explicitly supplied finite prefix is essential: arbitrary tapes need
not contain a double zero to the left of the head. This theorem does not
establish that a blank-start computation reaches the supplied configuration. -/

namespace Shared.Beeping.NPcoNP.NativeHalfReturn23
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfRows

theorem row23_zero : machine.table.row 23 false = ⟨false, .left, 24, false⟩ := by decide
theorem row23_one : machine.table.row 23 true = ⟨true, .left, 23, false⟩ := by decide
theorem row24_zero : machine.table.row 24 false = ⟨false, .left, 1, false⟩ := by decide
theorem row24_one : machine.table.row 24 true = ⟨true, .left, 23, false⟩ := by decide

theorem step23_zero (h : Int) (t : Int → Bool) (ht : t h = false) :
    machine.step (cfg 23 h t) = (cfg 24 (h-1) t, false) := by
  have hw : (⟨23, h, t⟩ : Config 284).write false = t := by rw [← ht]; exact write_current _
  simp [cfg, Machine.step, ht, row23_zero, Move.apply, hw]

theorem step23_one (h : Int) (t : Int → Bool) (ht : t h = true) :
    machine.step (cfg 23 h t) = (cfg 23 (h-1) t, false) := by
  have hw : (⟨23, h, t⟩ : Config 284).write true = t := by rw [← ht]; exact write_current _
  simp [cfg, Machine.step, ht, row23_one, Move.apply, hw]

theorem step24_zero (h : Int) (t : Int → Bool) (ht : t h = false) :
    machine.step (cfg 24 h t) = (cfg 1 (h-1) t, false) := by
  have hw : (⟨24, h, t⟩ : Config 284).write false = t := by rw [← ht]; exact write_current _
  simp [cfg, Machine.step, ht, row24_zero, Move.apply, hw]

theorem step24_one (h : Int) (t : Int → Bool) (ht : t h = true) :
    machine.step (cfg 24 h t) = (cfg 23 (h-1) t, false) := by
  have hw : (⟨24, h, t⟩ : Config 284).write true = t := by rw [← ht]; exact write_current _
  simp [cfg, Machine.step, ht, row24_one, Move.apply, hw]

/-- From a finite zero-pair-free descending prefix followed by two zeroes,
the literal machine takes exactly `length + 2` silent steps to state 1,
ending immediately left of the pair and preserving the entire tape. -/
theorem return_scan (s : Shape) (h : Int) (t : Int → Bool)
    (hm : downHolds t h (bits s ++ [false,false])) :
    silentSegment machine (cfg 23 h t)
      (cfg 1 (h - (bits s).length - 2) t) ((bits s).length + 2) := by
  induction s generalizing h with
  | stop =>
    simp only [bits, List.nil_append, downHolds] at hm
    have sa := oneSeg machine _ _ (step23_zero h t hm.1)
    have sb := oneSeg machine _ _ (step24_zero (h-1) t hm.2.1)
    have result := segAdd machine _ _ _ 1 1 sa sb
    simpa [bits, Int.sub_sub] using result
  | one s ih =>
    simp only [bits, List.cons_append, downHolds] at hm
    have sa := oneSeg machine _ _ (step23_one h t hm.1)
    have sh := ih (h-1) hm.2
    have result := segAdd machine _ _ _ 1 ((bits s).length+2) sa sh
    simpa [bits, List.length_cons, Int.sub_sub, Int.add_assoc, Int.add_comm,
      Int.add_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result
  | zeroOne s ih =>
    simp only [bits, List.cons_append, downHolds] at hm
    have sa := oneSeg machine _ _ (step23_zero h t hm.1)
    have sb := oneSeg machine _ _ (step24_one (h-1) t hm.2.1)
    have sh := ih (h-1-1) hm.2.2
    have sab := segAdd machine _ _ _ 1 1 sa sb
    have result := segAdd machine _ _ _ (1+1) ((bits s).length+2) sab sh
    have he : h - ((bits (Shape.zeroOne s)).length : Int) - 2 =
        h - 1 - 1 - (bits s).length - 2 := by simp [bits]; omega
    have hk : (bits (Shape.zeroOne s)).length + 2 =
        (1+1) + ((bits s).length+2) := by simp [bits]; omega
    rw [he, hk]
    exact result

theorem return_scan_positive (s : Shape) : 0 < (bits s).length + 2 := by omega

theorem return_scan_no_beep (s : Shape) (h : Int) (t : Int → Bool)
    (hm : downHolds t h (bits s ++ [false,false])) (j : Nat)
    (hj : j < (bits s).length + 2) :
    ¬ machine.system.BeepFrom (cfg 23 h t) j :=
  silent_no_beep machine _ _ _ j (return_scan s h t hm) hj

end Shared.Beeping.NPcoNP.NativeHalfReturn23
