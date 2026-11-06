import Shared.Beeping.NPcoNP.NativeManySweep

/-! Exact rightward state-18/19 scan of an arbitrary finite word with no
adjacent zeroes, ending at a supplied double-zero delimiter. -/
namespace Shared.Beeping.NPcoNP.NativeManyForward
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeManyShift
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem row18_one : machine.table.row 18 true = ⟨true,.right,18,false⟩ := by decide
theorem row19_one : machine.table.row 19 true = ⟨true,.right,18,false⟩ := by decide

theorem step18_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 18 h t)=(cfg 18 (h+1) t,false) := by
  have hw : (⟨18,h,t⟩ : Config 284).write true=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row18_one,Move.apply,hw]

theorem step19_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 19 h t)=(cfg 18 (h+1) t,false) := by
  have hw : (⟨19,h,t⟩ : Config 284).write true=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row19_one,Move.apply,hw]

/-- Every scanned bit costs one transition; the two-zero terminator costs
exactly two more. The entire tape is unchanged. -/
theorem scan18 (s : Shape) (h : Int) (t : Int → Bool)
    (hm : Holds t h (bits s ++ [false,false])) :
    silentSegment machine (cfg 18 h t)
      (cfg 20 (h+(bits s).length) t) ((bits s).length+2) := by
  induction s generalizing h with
  | stop =>
    simp only [bits,List.nil_append,Holds] at hm
    have sa := oneSeg machine _ _ (step18_0 h t hm.1)
    have sb := oneSeg machine _ _ (step19_0 (h+1) t hm.2.1)
    have res := segAdd machine _ _ _ 1 1 sa sb
    simpa [bits] using res
  | one s ih =>
    simp only [bits,List.cons_append,Holds] at hm
    have sa := oneSeg machine _ _ (step18_one h t hm.1)
    have sh := ih (h+1) hm.2
    have res := segAdd machine _ _ _ 1 ((bits s).length+2) sa sh
    simpa [bits,List.length_cons,Int.add_assoc,Int.add_comm,Int.add_left_comm,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using res
  | zeroOne s ih =>
    simp only [bits,List.cons_append,Holds] at hm
    have sa := oneSeg machine _ _ (step18_0 h t hm.1)
    have sb := oneSeg machine _ _ (step19_one (h+1) t hm.2.1)
    have sh := ih (h+1+1) hm.2.2
    have sab := segAdd machine _ _ _ 1 1 sa sb
    have res := segAdd machine _ _ _ 2 ((bits s).length+2) sab sh
    have he : h+1+1+((bits s).length : Int)=h+((bits (Shape.zeroOne s)).length : Int) := by
      simp only [bits,List.length_cons,Nat.cast_succ]
      omega
    have hc : 2+((bits s).length+2)=(bits (Shape.zeroOne s)).length+2 := by simp [bits]; omega
    rw [he,hc] at res
    exact res

/-- An unbounded one-tail can keep the scan in state 18 forever. This
counterexample is on an arbitrary tape, not a claimed blank-start execution. -/
theorem unbounded_one_scan (h : Int) (t : Int → Bool)
    (ones : ∀ p, h≤p → t p=true) (n : Nat) :
    silentSegment machine (cfg 18 h t) (cfg 18 (h+(n : Int)) t) n := by
  induction n with
  | zero => simp [silentSegment,W,WordEventSystem.advance,WordEventSystem.wordFrom]
  | succ n ih =>
    have hr : t (h+(n : Int))=true := ones _ (by omega)
    have hs := oneSeg machine _ _ (step18_one (h+(n : Int)) t hr)
    have hseg := segAdd machine _ _ _ n 1 ih hs
    simpa [Nat.cast_succ,Int.add_assoc,Nat.add_comm] using hseg

theorem unbounded_one_never_reaches_20 (h : Int) (t : Int → Bool)
    (ones : ∀ p, h≤p → t p=true) (n : Nat) :
    ((W machine).advance (cfg 18 h t) n).state ≠ 20 := by
  have hs := unbounded_one_scan h t ones n
  rw [hs.1]
  change (18 : Fin 284) ≠ 20
  decide

#print axioms scan18
#print axioms unbounded_one_never_reaches_20
end Shared.Beeping.NPcoNP.NativeManyForward
