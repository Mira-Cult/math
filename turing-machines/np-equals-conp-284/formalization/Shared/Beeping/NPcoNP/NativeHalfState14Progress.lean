import Shared.Beeping.NPcoNP.NativeHalfState12Progress

/-! Progress through the literal state-14 scan, which writes a one at its
zero delimiter. Progress after state 22 and entry reachability are separate. -/
namespace Shared.Beeping.NPcoNP.NativeHalfState14Progress

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState28Progress
open Shared.Beeping.NPcoNP.NativeHalfState12Progress

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def setAt (p : Int) (tape : Int → Bool) : Int → Bool :=
  fun i => if i=p then true else tape i

theorem row14_zero : machine.table.row 14 false = ⟨true, .right, 22, false⟩ := by decide
theorem row14_one : machine.table.row 14 true = ⟨true, .right, 14, false⟩ := by decide

theorem step14_zero (h : Int) (tape : Int → Bool) (ht : tape h=false) :
    machine.step (cfg 14 h tape) = (cfg 22 (h+1) (setAt h tape), false) := by
  have hw : (⟨14,h,tape⟩ : Config 284).write true = setAt h tape := rfl
  simp [cfg, Machine.step, ht, row14_zero, Move.apply, hw]

theorem step14_one (h : Int) (tape : Int → Bool) (ht : tape h=true) :
    machine.step (cfg 14 h tape) = (cfg 14 (h+1) tape, false) := by
  have hw : (⟨14,h,tape⟩ : Config 284).write true = tape := by
    rw [← ht]
    exact write_current _
  simp [cfg, Machine.step, ht, row14_one, Move.apply, hw]

/-- Every actual state-14 visit reaches state 22 in finite positive silent
time, with the exact write to the first encountered zero recorded. -/
theorem reachable_14_to_22 (time : Nat) (hstate : (machine.system.run time).state=14) :
    ∃ (n : Nat) (p : Int), 0<n ∧
      silentSegment machine (machine.system.run time)
        (cfg 22 (p+1) (setAt p (machine.system.run time).tape)) n := by
  obtain ⟨b,hb⟩ := run_has_right_zero time
  let h := (machine.system.run time).head
  let tape := (machine.system.run time).tape
  let k := (max b h-h).toNat
  have hk : b ≤ h+(k : Int) := by
    have hn : 0 ≤ max b h-h := by omega
    have he : (k : Int)=max b h-h := Int.toNat_of_nonneg hn
    omega
  have hz : ∀ p ≥ h+(k : Int), tape p=false := by
    intro p hp
    exact hb p (le_trans hk hp)
  obtain ⟨n,p,hn,_,_,_,hseg⟩ :=
    PhysicalOnesScan.tail_write machine 14 22 setAt step14_one step14_zero k h tape hz
  have hcfg : machine.system.run time = cfg 14 h tape := by
    cases hc : machine.system.run time with
    | mk state head cells =>
      simp only [hc,cfg] at hstate ⊢
      simp only [h,tape,hc,cfg] at *
      cases hstate
      rfl
  exact ⟨n,p,hn,by rw [hcfg]; exact hseg⟩

/-- Each actual state-261 visit reading one reaches state 22 in positive
finite silent time, composing all three literal control segments. -/
theorem reachable_261_one_to_22 (time : Nat)
    (hstate : (machine.system.run time).state=261)
    (hone : (machine.system.run time).tape (machine.system.run time).head=true) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=22 ∧
      silentSegment machine (machine.system.run time) e n := by
  obtain ⟨m,c,hm,hc,hseg⟩ := reachable_261_one_to_14 time hstate hone
  have hrun : machine.system.run (time+m)=c := by
    rw [EventSystem.run_add, ← ScalarWordRefinement.advance_ofBeep]
    exact hseg.1
  have h14 : (machine.system.run (time+m)).state=14 := by rw [hrun]; exact hc
  obtain ⟨n,p,hn,hmore⟩ := reachable_14_to_22 (time+m) h14
  refine ⟨m+n,cfg 22 (p+1) (setAt p (machine.system.run (time+m)).tape),
    by omega,rfl,?_⟩
  apply segAdd machine _ _ _ m n hseg
  rw [← hrun]
  exact hmore

end Shared.Beeping.NPcoNP.NativeHalfState14Progress

#print axioms Shared.Beeping.NPcoNP.NativeHalfState14Progress.reachable_14_to_22
#print axioms Shared.Beeping.NPcoNP.NativeHalfState14Progress.reachable_261_one_to_22
