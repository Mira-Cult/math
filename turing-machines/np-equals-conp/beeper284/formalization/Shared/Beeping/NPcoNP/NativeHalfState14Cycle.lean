import Shared.Beeping.NPcoNP.NativeHalfState14Progress

/-! Positive finite progress for the actual 14/22 loop. Each iteration
moves right; a finite zero tail forces exit to state 23. This does not prove
the subsequent program correct or establish an infinite-run simulation. -/
namespace Shared.Beeping.NPcoNP.NativeHalfState14Cycle

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState28Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState12Progress
open Shared.Beeping.NPcoNP.NativeHalfState14Progress

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem row22_zero : machine.table.row 22 false = ⟨false, .left, 23, false⟩ := by decide
theorem row22_one : machine.table.row 22 true = ⟨false, .right, 14, false⟩ := by decide

theorem step22_zero (h : Int) (tape : Int → Bool) (ht : tape h=false) :
    machine.step (cfg 22 h tape) = (cfg 23 (h-1) tape, false) := by
  have hw : (⟨22,h,tape⟩ : Config 284).write false = tape := by
    rw [← ht]
    exact write_current _
  simp [cfg, Machine.step, ht, row22_zero, Move.apply, hw]

theorem step22_one (h : Int) (tape : Int → Bool) (ht : tape h=true) :
    machine.step (cfg 22 h tape) = (cfg 14 (h+1) (clearAt h tape), false) := by
  have hw : (⟨22,h,tape⟩ : Config 284).write false = clearAt h tape := rfl
  simp [cfg, Machine.step, ht, row22_one, Move.apply, hw]

theorem finish (h : Int) (tape : Int → Bool)
    (h0 : tape h=false) (h1 : tape (h+1)=false) :
    silentSegment machine (cfg 14 h tape) (cfg 23 h (setAt h tape)) 2 := by
  have hn : h+1 ≠ h := by omega
  have ht : setAt h tape (h+1)=false := by simp [setAt,hn,h1]
  have ha := oneSeg machine _ _ (step14_zero h tape h0)
  have hb := oneSeg machine _ _ (step22_zero (h+1) (setAt h tape) ht)
  have hc := segAdd machine _ _ _ 1 1 ha hb
  simpa [Int.add_assoc] using hc

theorem restart (h : Int) (tape : Int → Bool)
    (h0 : tape h=false) (h1 : tape (h+1)=true) :
    silentSegment machine (cfg 14 h tape)
      (cfg 14 (h+2) (clearAt (h+1) (setAt h tape))) 2 := by
  have hn : h+1 ≠ h := by omega
  have ht : setAt h tape (h+1)=true := by simp [setAt,hn,h1]
  have ha := oneSeg machine _ _ (step14_zero h tape h0)
  have hb := oneSeg machine _ _ (step22_one (h+1) (setAt h tape) ht)
  have hc := segAdd machine _ _ _ 1 1 ha hb
  simpa [Int.add_assoc] using hc

/-- A right-zero tail bounds the number of literal transitions in the
14/22 loop and excludes silent divergence. -/
theorem cycle_tail (k : Nat) (h : Int) (tape : Int → Bool)
    (hz : ∀ p ≥ h+(k : Int), tape p=false) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ n≤2*k+2 ∧ e.state=23 ∧
      silentSegment machine (cfg 14 h tape) e n := by
  induction k generalizing h tape with
  | zero =>
    have h0 : tape h=false := hz h (by simp)
    have h1 : tape (h+1)=false := hz (h+1) (by simp)
    exact ⟨2,cfg 23 h (setAt h tape),by omega,by omega,rfl,finish h tape h0 h1⟩
  | succ k ih =>
    cases h0 : tape h with
    | true =>
      have hz' : ∀ p ≥ (h+1)+(k : Int), tape p=false := by
        intro p hp
        apply hz p
        push_cast at *
        omega
      obtain ⟨n,e,hn,hbound,he,hseg⟩ := ih (h+1) tape hz'
      exact ⟨1+n,e,by omega,by omega,he,
        segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step14_one h tape h0)) hseg⟩
    | false =>
      cases h1 : tape (h+1) with
      | false =>
        exact ⟨2,cfg 23 h (setAt h tape),by omega,by omega,rfl,finish h tape h0 h1⟩
      | true =>
        let tape' := clearAt (h+1) (setAt h tape)
        have hz' : ∀ p ≥ (h+2)+(k : Int), tape' p=false := by
          intro p hp
          have hp0 : p ≠ h := by omega
          have hp1 : p ≠ h+1 := by omega
          have hpz : tape p=false := by
            apply hz p
            push_cast at *
            omega
          simp [tape',clearAt,setAt,hp0,hp1,hpz]
        obtain ⟨n,e,hn,hbound,he,hseg⟩ := ih (h+2) tape' hz'
        exact ⟨2+n,e,by omega,by omega,he,
          segAdd machine _ _ _ 2 n (restart h tape h0 h1) hseg⟩

/-- Every actual state-14 visit exits the 14/22 loop in finite positive
silent time, using the finite support of the blank-start run. -/
theorem reachable_14_to_23 (time : Nat) (hstate : (machine.system.run time).state=14) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=23 ∧
      silentSegment machine (machine.system.run time) e n := by
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
  obtain ⟨n,e,hn,_,he,hseg⟩ := cycle_tail k h tape hz
  have hcfg : machine.system.run time = cfg 14 h tape := by
    cases hc : machine.system.run time with
    | mk state head cells =>
      simp only [hc,cfg] at hstate ⊢
      simp only [h,tape,hc,cfg] at *
      cases hstate
      rfl
  exact ⟨n,e,hn,he,by rw [hcfg]; exact hseg⟩

/-- The state-261 one-branch reaches the exit of the 14/22 loop in
positive finite silent time on the actual blank-start run. -/
theorem reachable_261_one_to_23 (time : Nat)
    (hstate : (machine.system.run time).state=261)
    (hone : (machine.system.run time).tape (machine.system.run time).head=true) :
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=23 ∧
      silentSegment machine (machine.system.run time) e n := by
  obtain ⟨m,c,hm,hc,hseg⟩ := reachable_261_one_to_14 time hstate hone
  have hrun : machine.system.run (time+m)=c := by
    rw [EventSystem.run_add, ← ScalarWordRefinement.advance_ofBeep]
    exact hseg.1
  have h14 : (machine.system.run (time+m)).state=14 := by rw [hrun]; exact hc
  obtain ⟨n,e,hn,he,hmore⟩ := reachable_14_to_23 (time+m) h14
  refine ⟨m+n,e,by omega,he,?_⟩
  apply segAdd machine _ _ _ m n hseg
  rw [← hrun]
  exact hmore

end Shared.Beeping.NPcoNP.NativeHalfState14Cycle

#print axioms Shared.Beeping.NPcoNP.NativeHalfState14Cycle.cycle_tail
#print axioms Shared.Beeping.NPcoNP.NativeHalfState14Cycle.reachable_14_to_23
#print axioms Shared.Beeping.NPcoNP.NativeHalfState14Cycle.reachable_261_one_to_23
