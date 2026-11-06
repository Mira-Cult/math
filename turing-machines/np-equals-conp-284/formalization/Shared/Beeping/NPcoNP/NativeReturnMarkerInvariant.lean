import Shared.Beeping.NPcoNP.NativeReturnIncoming
import Shared.Beeping.NPcoNP.NativeHalfState1Scan
import Shared.Beeping.NPcoNP.NativeHalfState27Scan

/-! A blank-start invariant for the literal return scanner. -/
namespace Shared.Beeping.NPcoNP.NativeReturnMarkerInvariant
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState27Scan
open Shared.Beeping.NPcoNP.NativeHalfState28Progress
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 20000000

def ReturnInvariant (c : Config 284) : Prop :=
  (c.state=27 → ∃ p : Int, p<c.head ∧ c.tape p=true) ∧
  (c.state=28 → ∃ p : Int, p<c.head-1 ∧ c.tape p=true)

theorem step_invariant (c : Config 284) (hinv : ReturnInvariant c) :
    ReturnInvariant (machine.step c).1 := by
  rcases c with ⟨q,h,tape⟩
  rcases hinv with ⟨hi27,hi28⟩
  constructor
  · intro htarget
    have hn : (machine.table.row q (tape h)).next=27 := htarget
    rcases incoming27 q (tape h) hn with ⟨hq,hread⟩ | ⟨hq,hread⟩
    · subst q
      have hs := NativeHalfState1Scan.step_zero h tape hread
      change ∃ p : Int, p < (machine.step (cfg 1 h tape)).1.head ∧
        (machine.step (cfg 1 h tape)).1.tape p=true
      rw [hs]
      exact ⟨h,by simp [cfg],by simp [cfg,put]⟩
    · subst q
      obtain ⟨p,hp,hm⟩ := hi27 rfl
      change p<h at hp
      change tape p=true at hm
      have hs := NativeHalfState27Scan.step27_zero h tape hread
      change ∃ p : Int, p < (machine.step (cfg 27 h tape)).1.head ∧
        (machine.step (cfg 27 h tape)).1.tape p=true
      rw [hs]
      exact ⟨p,by simp only [cfg]; omega,hm⟩
  · intro htarget
    have hn : (machine.table.row q (tape h)).next=28 := htarget
    rcases incoming28 q (tape h) hn with ⟨hq,hread⟩ | ⟨hq,hread⟩
    · subst q
      obtain ⟨p,hp,hm⟩ := hi27 rfl
      change p<h at hp
      change tape p=true at hm
      have hs := NativeHalfState27Scan.step27_one h tape hread
      change ∃ p : Int, p < (machine.step (cfg 27 h tape)).1.head-1 ∧
        (machine.step (cfg 27 h tape)).1.tape p=true
      rw [hs]
      refine ⟨p,by simp only [cfg]; omega,?_⟩
      change put tape h false p=true
      rw [put_other _ _ _ _ (by omega)]
      exact hm
    · subst q
      obtain ⟨p,hp,hm⟩ := hi28 rfl
      change p<h-1 at hp
      change tape p=true at hm
      have hs := NativeHalfState28Progress.step28_one h tape hread
      change ∃ p : Int, p < (machine.step (cfg 28 h tape)).1.head-1 ∧
        (machine.step (cfg 28 h tape)).1.tape p=true
      rw [hs]
      refine ⟨p,by simp only [cfg]; omega,?_⟩
      change put tape h false p=true
      rw [put_other _ _ _ _ (by omega)]
      exact hm

theorem run_invariant (time : Nat) : ReturnInvariant (machine.system.run time) := by
  induction time with
  | zero =>
    constructor <;> intro h
    · have hs : (machine.system.run 0).state.val=0 := machine_starts_zero.1
      have hv := congrArg Fin.val h
      rw [hs] at hv
      contradiction
    · have hs : (machine.system.run 0).state.val=0 := machine_starts_zero.1
      have hv := congrArg Fin.val h
      rw [hs] at hv
      contradiction
  | succ time ih =>
    change ReturnInvariant (machine.step (machine.system.run time)).1
    exact step_invariant _ ih

#print axioms run_invariant
end Shared.Beeping.NPcoNP.NativeReturnMarkerInvariant
