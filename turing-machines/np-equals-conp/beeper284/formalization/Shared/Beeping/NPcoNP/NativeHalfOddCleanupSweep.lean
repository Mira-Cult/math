import Shared.Beeping.NPcoNP.NativeHalfSweepSpec

/-! Exact backward cleanup for the odd native-HALF branch. This covers
the literal state-38/39 sweep through state 25 on a supplied finite tape
pattern; it does not assert reachability or a complete HALF operation. -/
namespace Shared.Beeping.NPcoNP.NativeHalfOddCleanupSweep

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfRows

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem row38_zero : machine.table.row 38 false = ⟨true,.left,39,false⟩ := by decide
theorem row38_one : machine.table.row 38 true = ⟨true,.left,38,false⟩ := by decide
theorem row39_zero : machine.table.row 39 false = ⟨false,.left,25,false⟩ := by decide
theorem row39_one : machine.table.row 39 true = ⟨false,.left,38,false⟩ := by decide

theorem step38_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 38 h t)=(cfg 39 (h-1) (put t h true),false) := by
  have hw : (⟨38,h,t⟩ : Config 284).write true=put t h true := rfl
  simp [cfg,Machine.step,ht,row38_zero,Move.apply,hw]

theorem step38_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 38 h t)=(cfg 38 (h-1) t,false) := by
  have hw : (⟨38,h,t⟩ : Config 284).write true=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row38_one,Move.apply,hw]

theorem step39_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 39 h t)=(cfg 25 (h-1) t,false) := by
  have hw : (⟨39,h,t⟩ : Config 284).write false=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row39_zero,Move.apply,hw]

theorem step39_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 39 h t)=(cfg 38 (h-1) (put t h false),false) := by
  have hw : (⟨39,h,t⟩ : Config 284).write false=put t h false := rfl
  simp [cfg,Machine.step,ht,row39_one,Move.apply,hw]

/-- On the supplied reverse pattern the odd cleanup reaches state 25 in
exactly one step per bit plus two, with the existing whole-tape effect. -/
theorem odd_cleanup_effect (s : Shape) (h : Int) (t : Int → Bool)
    (hm : downHolds t h (bits s ++ [false,false])) :
    silentSegment machine (cfg 38 h t)
      (cfg 25 (h-(bits s).length-2) (effect s t h)) ((bits s).length+2) := by
  induction s generalizing h t with
  | stop =>
    simp only [bits,List.nil_append,downHolds] at hm
    have h0 : put t h true (h-1)=false := by rw [put_other _ _ _ _ (by omega)]; exact hm.2.1
    have sa := oneSeg machine _ _ (step38_zero h t hm.1)
    have sb := oneSeg machine _ _ (step39_zero (h-1) (put t h true) h0)
    have res := segAdd machine _ _ _ 1 1 sa sb
    simpa [bits,effect,cfg,Int.sub_sub] using res
  | one s ih =>
    simp only [bits,List.cons_append,downHolds] at hm
    have sa := oneSeg machine _ _ (step38_one h t hm.1)
    have sh := ih (h-1) t hm.2
    have res := segAdd machine _ _ _ 1 ((bits s).length+2) sa sh
    simpa [bits,effect,cfg,List.length_cons,Int.sub_sub,Int.add_assoc,Int.add_comm,
      Int.add_left_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using res
  | zeroOne s ih =>
    simp only [bits,List.cons_append,downHolds] at hm
    have h1 : put t h true (h-1)=true := by rw [put_other _ _ _ _ (by omega)]; exact hm.2.1
    have sa := oneSeg machine _ _ (step38_zero h t hm.1)
    have sb := oneSeg machine _ _ (step39_one (h-1) (put t h true) h1)
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

/-- The odd cleanup has the same pointwise full-tape shift specification as
the even cleanup. -/
theorem odd_cleanup_sweep (s : Shape) (h : Int) (t : Int → Bool)
    (hm : downHolds t h (bits s ++ [false,false])) :
    silentSegment machine (cfg 38 h t)
      (cfg 25 (h-(bits s).length-2) (spec t h (bits s).length))
      ((bits s).length+2) := by
  rw [← effect_eq_spec s h t hm]
  exact odd_cleanup_effect s h t hm

end Shared.Beeping.NPcoNP.NativeHalfOddCleanupSweep

#print axioms Shared.Beeping.NPcoNP.NativeHalfOddCleanupSweep.odd_cleanup_sweep
