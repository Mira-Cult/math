import Shared.Beeping.NPcoNP.NativeHalfState16Progress

/-! Progress from the literal state-12 right scan, including composition
with the state-261 one-branch. This does not prove reachability of either
entry or progress after state 14. -/
namespace Shared.Beeping.NPcoNP.NativeHalfState12Progress

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState28Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem row12_zero : machine.table.row 12 false = ⟨false, .right, 14, false⟩ := by decide
theorem row12_one : machine.table.row 12 true = ⟨true, .right, 12, false⟩ := by decide

theorem step12_zero (h : Int) (tape : Int → Bool) (ht : tape h = false) :
    machine.step (cfg 12 h tape) = (cfg 14 (h+1) tape, false) := by
  have hw : (⟨12,h,tape⟩ : Config 284).write false = tape := by
    rw [← ht]
    exact write_current _
  simp [cfg, Machine.step, ht, row12_zero, Move.apply, hw]

theorem step12_one (h : Int) (tape : Int → Bool) (ht : tape h = true) :
    machine.step (cfg 12 h tape) = (cfg 12 (h+1) tape, false) := by
  have hw : (⟨12,h,tape⟩ : Config 284).write true = tape := by
    rw [← ht]
    exact write_current _
  simp [cfg, Machine.step, ht, row12_one, Move.apply, hw]

/-- Every actual visit to state 12 reaches state 14 in finite positive
silent time. The tape is unchanged throughout the scanned segment. -/
theorem reachable_12_to_14 (time : Nat) (hstate : (machine.system.run time).state = 12) :
    ∃ (m : Nat) (e : Config 284), 0<m ∧ e.state=14 ∧
      e.tape=(machine.system.run time).tape ∧
      silentSegment machine (machine.system.run time) e m := by
  obtain ⟨b, hb⟩ := run_has_right_zero time
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
  obtain ⟨m, hm, _, hseg⟩ :=
    PhysicalOnesScan.tail machine 12 14 step12_one step12_zero k h tape hz
  have hcfg : machine.system.run time = cfg 12 h tape := by
    cases hc : machine.system.run time with
    | mk state head cells =>
      simp only [hc,cfg] at hstate ⊢
      simp only [h,tape,hc,cfg] at *
      cases hstate
      rfl
  exact ⟨m, cfg 14 (h+m) tape, hm, rfl, rfl, by rw [hcfg]; exact hseg⟩

/-- The actual state-261 one-branch reaches state 14 after a positive finite
silent segment. This combines both scans and accounts for the full run. -/
theorem reachable_261_one_to_14 (time : Nat)
    (hstate : (machine.system.run time).state = 261)
    (hone : (machine.system.run time).tape (machine.system.run time).head = true) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=14 ∧
      silentSegment machine (machine.system.run time) e n := by
  obtain ⟨m,c,hm,hc,hseg⟩ := reachable_261_one_to_12 time hstate hone
  have hrun : machine.system.run (time+m)=c := by
    rw [EventSystem.run_add, ← ScalarWordRefinement.advance_ofBeep]
    exact hseg.1
  have h12 : (machine.system.run (time+m)).state=12 := by rw [hrun]; exact hc
  obtain ⟨n,e,hn,he,_,hmore⟩ := reachable_12_to_14 (time+m) h12
  refine ⟨m+n,e,by omega,he,?_⟩
  apply segAdd machine _ _ _ m n hseg
  rw [← hrun]
  exact hmore

end Shared.Beeping.NPcoNP.NativeHalfState12Progress

#print axioms Shared.Beeping.NPcoNP.NativeHalfState12Progress.reachable_12_to_14
#print axioms Shared.Beeping.NPcoNP.NativeHalfState12Progress.reachable_261_one_to_14
