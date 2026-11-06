import Shared.Beeping.NPcoNP.NativeHalfState28Progress
import Shared.Beeping.NPcoNP.NativeHalfState28Incoming

/-! The physical state-28 scan erases ones until it sees a zero. Every
actual blank-start entry to state 28 has a zero immediately left of the
head: every table row entering state 28 writes zero and moves right. The
scan then arrives at state 6 over a zero and takes its silent zero row to
state 97. This does not prove state 28 is reached, nor progress after 97. -/

namespace Shared.Beeping.NPcoNP.NativeHalfState28Exit

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState28Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Incoming

set_option maxRecDepth 32768
set_option maxHeartbeats 20000000

/-- The cell immediately left of the head is zero whenever the actual run
is in state 28. This uses the previous transition, not a guessed tape layout. -/
theorem reachable_28_left_zero (time : Nat)
    (hstate : (machine.system.run time).state = 28) :
    (machine.system.run time).tape ((machine.system.run time).head - 1) = false := by
  cases time with
  | zero =>
    have hs : (machine.system.run 0).state.val = 0 := machine_starts_zero.1
    have hv := congrArg Fin.val hstate
    rw [hs] at hv
    contradiction
  | succ time =>
    let c := machine.system.run time
    let r := machine.table.row c.state (c.tape c.head)
    have hn : r.next = 28 := by
      change ((machine.step c).1).state = 28 at hstate
      exact hstate
    obtain ⟨hw, hm⟩ := enters28_write_left_zero c.state (c.tape c.head) hn
    change ((machine.step c).1).tape (((machine.step c).1).head - 1) = false
    simp [Machine.step, r, hm, hw, Move.apply, Config.write]

/-- A zero within distance `k`, together with the zero immediately left of
the initial head, guarantees that the state-6 exit reads zero. -/
theorem scan_to_zero_left (k : Nat) (h : Int) (t : Int → Bool)
    (hleft : t (h-1) = false) (hz : t (h + (k : Int)) = false) :
    ∃ (n : Nat) (e : Config 284), 0 < n ∧ n ≤ k+1 ∧ e.state = 6 ∧
      e.tape e.head = false ∧ silentSegment machine (cfg 28 h t) e n := by
  induction k generalizing h t with
  | zero =>
    refine ⟨1, cfg 6 (h-1) t, by omega, by omega, rfl, hleft, ?_⟩
    exact oneSeg machine _ _ (step28_zero h t (by simpa using hz))
  | succ k ih =>
    cases hv : t h with
    | false =>
      refine ⟨1, cfg 6 (h-1) t, by omega, by omega, rfl, hleft, ?_⟩
      exact oneSeg machine _ _ (step28_zero h t hv)
    | true =>
      have hneq : h+1+(k : Int) ≠ h := by omega
      have hz' : put t h false ((h+1)+(k : Int)) = false := by
        have he : h+1+(k:Int) = h+((Nat.succ k:Nat):Int) := by push_cast; omega
        rw [put_other _ _ _ _ hneq, he]
        exact hz
      have hleft' : put t h false ((h+1)-1) = false := by simp [put]
      obtain ⟨n, e, hn, hb, he, ht, hs⟩ := ih (h+1) (put t h false) hleft' hz'
      refine ⟨1+n, e, by omega, by omega, he, ht, ?_⟩
      exact segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step28_one h t hv)) hs

theorem row6_zero : machine.table.row 6 false = ⟨true, .left, 97, false⟩ := by decide

theorem step6_zero (h : Int) (t : Int → Bool) (ht : t h = false) :
    machine.step (cfg 6 h t) = (cfg 97 (h-1) (put t h true), false) := by
  change machine.step ⟨6,h,t⟩ = (⟨97,h-1,put t h true⟩,false)
  have hw : (⟨6,h,t⟩ : Config 284).write true = put t h true := rfl
  simp [Machine.step, ht, row6_zero, Move.apply, hw]

/-- Whenever the actual run reaches state 28, it reaches state 97 after a
strictly positive finite segment with no beeps. -/
theorem reachable_28_to_97 (time : Nat)
    (hstate : (machine.system.run time).state = 28) :
    ∃ (n : Nat) (e : Config 284), 0 < n ∧ e.state = 97 ∧
      silentSegment machine (machine.system.run time) e n := by
  obtain ⟨b, hb⟩ := run_has_right_zero time
  let h := (machine.system.run time).head
  let k := (max b h - h).toNat
  have hk : b ≤ h + (k : Int) := by
    have hn : 0 ≤ max b h - h := by omega
    have ht : (k : Int) = max b h - h := Int.toNat_of_nonneg hn
    omega
  have hz : (machine.system.run time).tape (h + (k : Int)) = false := hb _ hk
  have hl : (machine.system.run time).tape (h-1) = false :=
    reachable_28_left_zero time hstate
  obtain ⟨n, c, hn, _, hc, ht, hs⟩ :=
    scan_to_zero_left k h (machine.system.run time).tape hl hz
  let e : Config 284 := cfg 97 (c.head-1) (put c.tape c.head true)
  have hcfg : c = cfg 6 c.head c.tape := by
    have he : c = cfg c.state c.head c.tape := by cases c; rfl
    simpa only [hc] using he
  have ht' : c.tape c.head = false := ht
  have hstep : machine.step c = (e,false) := by
    conv_lhs => rw [hcfg]
    exact step6_zero c.head c.tape ht'
  have hrun : machine.system.run time = cfg 28 h (machine.system.run time).tape := by
    cases hx : machine.system.run time with
    | mk state head tape =>
      simp only [hx, cfg] at hstate ⊢
      simp only [h, hx, cfg] at *
      cases hstate
      rfl
  refine ⟨n+1, e, by omega, rfl, ?_⟩
  rw [hrun]
  exact segAdd machine _ _ _ n 1 hs (oneSeg machine _ _ hstep)

end Shared.Beeping.NPcoNP.NativeHalfState28Exit
