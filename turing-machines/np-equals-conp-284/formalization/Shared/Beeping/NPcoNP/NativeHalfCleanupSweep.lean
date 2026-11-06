import Shared.Beeping.NPcoNP.NativeHalfSweepSpec

/-! The inherited decrement routine's reverse sweep, using the same tape
shape and pointwise effect as the native HALF suffix sweep. This is a local
prepared-configuration theorem, not a blank-start or complete HALF proof. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Shared.Beeping.NPcoNP.NativeHalfCleanupSweep
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.Table284

theorem row20_zero : machine.table.row 20 false = ⟨true, .left, 21, false⟩ := by decide
theorem row20_one : machine.table.row 20 true = ⟨true, .left, 20, false⟩ := by decide
theorem row21_zero : machine.table.row 21 false = ⟨false, .left, 23, false⟩ := by decide
theorem row21_one : machine.table.row 21 true = ⟨false, .left, 20, false⟩ := by decide

theorem step20_zero (h : Int) (t : Int → Bool) (ht : t h = false) :
    machine.step (cfg 20 h t) = (cfg 21 (h-1) (put t h true), false) := by
  change machine.step ⟨20, h, t⟩ = (⟨21, h-1, put t h true⟩, false)
  have hw : (⟨20, h, t⟩ : Config 284).write true = put t h true := rfl
  simp [Machine.step, ht, row20_zero, Move.apply, hw]

theorem step20_one (h : Int) (t : Int → Bool) (ht : t h = true) :
    machine.step (cfg 20 h t) = (cfg 20 (h-1) t, false) := by
  have hw : (⟨20, h, t⟩ : Config 284).write true = t := by rw [← ht]; exact write_current _
  simp [cfg, Machine.step, ht, row20_one, Move.apply, hw]

theorem step21_zero (h : Int) (t : Int → Bool) (ht : t h = false) :
    machine.step (cfg 21 h t) = (cfg 23 (h-1) t, false) := by
  have hw : (⟨21, h, t⟩ : Config 284).write false = t := by rw [← ht]; exact write_current _
  simp [cfg, Machine.step, ht, row21_zero, Move.apply, hw]

theorem step21_one (h : Int) (t : Int → Bool) (ht : t h = true) :
    machine.step (cfg 21 h t) = (cfg 20 (h-1) (put t h false), false) := by
  change machine.step ⟨21, h, t⟩ = (⟨20, h-1, put t h false⟩, false)
  have hw : (⟨21, h, t⟩ : Config 284).write false = put t h false := rfl
  simp [Machine.step, ht, row21_one, Move.apply, hw]

/-- A prepared reverse sweep takes exactly one transition per supplied bit
plus two delimiter transitions; it emits no beep and rewrites the whole tape
according to the existing sweep specification. -/
theorem cleanup_effect (s : Shape) (h : Int) (t : Int → Bool)
    (hm : downHolds t h (bits s ++ [false,false])) :
    silentSegment machine (cfg 20 h t)
      (cfg 23 (h - (bits s).length - 2) (effect s t h))
      ((bits s).length + 2) := by
  induction s generalizing h t with
  | stop =>
    simp only [bits, List.nil_append, downHolds] at hm
    have h0 : put t h true (h-1) = false := by rw [put_other _ _ _ _ (by omega)]; exact hm.2.1
    have sa := oneSeg machine _ _ (step20_zero h t hm.1)
    have sb := oneSeg machine _ _ (step21_zero (h-1) (put t h true) h0)
    have res := segAdd machine _ _ _ 1 1 sa sb
    simpa [bits,effect,cfg,Int.sub_sub] using res
  | one s ih =>
    simp only [bits, List.cons_append, downHolds] at hm
    have sa := oneSeg machine _ _ (step20_one h t hm.1)
    have sh := ih (h-1) t hm.2
    have res := segAdd machine _ _ _ 1 ((bits s).length+2) sa sh
    simpa [bits,effect,cfg, List.length_cons, Int.sub_sub, Int.add_assoc, Int.add_comm, Int.add_left_comm, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using res
  | zeroOne s ih =>
    simp only [bits, List.cons_append, downHolds] at hm
    have h1 : put t h true (h-1) = true := by rw [put_other _ _ _ _ (by omega)]; exact hm.2.1
    have sa := oneSeg machine _ _ (step20_zero h t hm.1)
    have sb := oneSeg machine _ _ (step21_one (h-1) (put t h true) h1)
    have htail : downHolds (put (put t h true) (h-1) false) (h-1-1) (bits s ++ [false,false]) := by
      apply downHolds_put
      · omega
      · apply downHolds_put
        · omega
        · exact hm.2.2
    have sh := ih (h-1-1) (put (put t h true) (h-1) false) htail
    have sab := segAdd machine _ _ _ 1 1 sa sb
    have res := segAdd machine _ _ _ (1+1) ((bits s).length+2) sab sh
    convert res using 1 <;> simp [bits,effect,cfg,List.length_cons,Int.sub_sub] <;> omega

theorem cleanup_sweep (s : Shape) (h : Int) (t : Int → Bool)
    (hm : downHolds t h (bits s ++ [false,false])) :
    silentSegment machine (cfg 20 h t)
      (cfg 23 (h - (bits s).length - 2) (spec t h (bits s).length))
      ((bits s).length + 2) := by
  rw [← effect_eq_spec s h t hm]
  exact cleanup_effect s h t hm

theorem cleanup_sweep_positive (s : Shape) : 0 < (bits s).length + 2 := by omega

theorem cleanup_sweep_no_beep (s : Shape) (h : Int) (t : Int → Bool)
    (hm : downHolds t h (bits s ++ [false,false])) (j : Nat)
    (hj : j < (bits s).length + 2) :
    ¬ machine.system.BeepFrom (cfg 20 h t) j :=
  silent_no_beep machine _ _ _ j (cleanup_sweep s h t hm) hj
end Shared.Beeping.NPcoNP.NativeHalfCleanupSweep
