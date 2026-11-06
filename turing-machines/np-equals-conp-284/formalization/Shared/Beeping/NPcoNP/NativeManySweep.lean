import Shared.Beeping.NPcoNP.NativeManyShift
import Shared.Beeping.NPcoNP.NativeHalfSweepSpec

/-! The many-selector path has the same backwards sweep as the native-HALF
path, but uses literal states 20 and 21 and exits to state 23. The entire
finite suffix is specified; the two final zeroes supply the stopping witness. -/
namespace Shared.Beeping.NPcoNP.NativeManySweep
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeManyShift
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem row20_one : machine.table.row 20 true = ⟨true,.left,20,false⟩ := by decide

theorem step20_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 20 h t)=(cfg 20 (h-1) t,false) := by
  have hw : (⟨20,h,t⟩ : Config 284).write true=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row20_one,Move.apply,hw]

/-- Exact backward scan over an arbitrary zero-pair-free finite word.
The tape effect is shared with, and proved independently of, the state-34
sweep; both trailing zeroes are required to guarantee exit. -/
theorem sweep20 (s : Shape) (h : Int) (t : Int → Bool)
    (hm : downHolds t h (bits s ++ [false,false])) :
    silentSegment machine (cfg 20 h t)
      (cfg 23 (h-(bits s).length-2) (effect s t h)) ((bits s).length+2) := by
  induction s generalizing h t with
  | stop =>
    simp only [bits,List.nil_append,downHolds] at hm
    have h0 : put t h true (h-1)=false := by rw [put_other _ _ _ _ (by omega)]; exact hm.2.1
    have sa := oneSeg machine _ _ (step20_0 h t hm.1)
    change silentSegment machine (cfg 20 h t) (cfg 21 (h-1) (put t h true)) 1 at sa
    have sb := oneSeg machine _ _ (step21_0 (h-1) (put t h true) h0)
    have res := segAdd machine _ _ _ 1 1 sa sb
    simpa [bits,effect,cfg,Int.sub_sub] using res
  | one s ih =>
    simp only [bits,List.cons_append,downHolds] at hm
    have sa := oneSeg machine _ _ (step20_one h t hm.1)
    have sh := ih (h-1) t hm.2
    have res := segAdd machine _ _ _ 1 ((bits s).length+2) sa sh
    simpa [bits,effect,cfg,List.length_cons,Int.sub_sub,Int.add_assoc,Int.add_comm,
      Int.add_left_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using res
  | zeroOne s ih =>
    simp only [bits,List.cons_append,downHolds] at hm
    have h1 : put t h true (h-1)=true := by rw [put_other _ _ _ _ (by omega)]; exact hm.2.1
    have sa := oneSeg machine _ _ (step20_0 h t hm.1)
    change silentSegment machine (cfg 20 h t) (cfg 21 (h-1) (put t h true)) 1 at sa
    have sb := oneSeg machine _ _ (step21_1 (h-1) (put t h true) h1)
    change silentSegment machine (cfg 21 (h-1) (put t h true))
      (cfg 20 (h-1-1) (put (put t h true) (h-1) false)) 1 at sb
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

/-- The backward sweep shifts every input bit in its entire finite interval
one cell left, sets the far-right endpoint, and leaves the remaining tape
untouched. This is a pointwise whole-tape statement. -/
theorem sweep20_spec (s : Shape) (h : Int) (t : Int → Bool)
    (hm : downHolds t h (bits s ++ [false,false])) :
    silentSegment machine (cfg 20 h t)
      (cfg 23 (h-(bits s).length-2) (spec t h (bits s).length)) ((bits s).length+2) := by
  rw [← effect_eq_spec s h t hm]
  exact sweep20 s h t hm

#print axioms sweep20_spec
end Shared.Beeping.NPcoNP.NativeManySweep
