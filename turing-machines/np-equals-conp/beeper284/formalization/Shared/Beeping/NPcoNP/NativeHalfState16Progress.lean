import Shared.Beeping.NPcoNP.NativeHalfScan
import Shared.Beeping.NPcoNP.NativeHalfState28Progress
import Shared.Beeping.NPcoNP.PhysicalOnesScan

/-! Literal state-16 scan.  This proves a positive finite silent segment
through any specified finite run of ones followed by zero, preserving the
entire tape.  Reachability of the delimiter from blank start is separate. -/

namespace Shared.Beeping.NPcoNP.NativeHalfState16Progress

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState28Progress

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem row16_zero : machine.table.row 16 false = ⟨false, .right, 12, false⟩ := by decide
theorem row16_one : machine.table.row 16 true = ⟨true, .right, 16, false⟩ := by decide
theorem row261_one : machine.table.row 261 true = ⟨false, .right, 16, false⟩ := by decide

def clearAt (p : Int) (tape : Int → Bool) : Int → Bool :=
  fun i => if i = p then false else tape i

theorem step261_one (h : Int) (tape : Int → Bool) (ht : tape h = true) :
    machine.step (cfg 261 h tape) = (cfg 16 (h+1) (clearAt h tape), false) := by
  have hw : (⟨261, h, tape⟩ : Config 284).write false = clearAt h tape := rfl
  simp [cfg, Machine.step, ht, row261_one, Move.apply, hw]

/-- Clearing a cell strictly to the left preserves any specified finite word. -/
theorem holds_clear_left (tape : Int → Bool) (p h : Int) (xs : List Bool)
    (hp : p < h) (ht : Holds tape h xs) : Holds (clearAt p tape) h xs := by
  induction xs generalizing h with
  | nil => trivial
  | cons x xs ih =>
    change tape h = x ∧ Holds tape (h+1) xs at ht
    change (if h=p then false else tape h) = x ∧ Holds (clearAt p tape) (h+1) xs
    exact ⟨by simp [ne_of_gt hp, ht.1], ih (h+1) (by omega) ht.2⟩

theorem step16_zero (h : Int) (tape : Int → Bool) (ht : tape h = false) :
    machine.step (cfg 16 h tape) = (cfg 12 (h+1) tape, false) := by
  have hw : (⟨16, h, tape⟩ : Config 284).write false = tape := by
    rw [← ht]
    exact write_current _
  simp [cfg, Machine.step, ht, row16_zero, Move.apply, hw]

theorem step16_one (h : Int) (tape : Int → Bool) (ht : tape h = true) :
    machine.step (cfg 16 h tape) = (cfg 16 (h+1) tape, false) := by
  have hw : (⟨16, h, tape⟩ : Config 284).write true = tape := by
    rw [← ht]
    exact write_current _
  simp [cfg, Machine.step, ht, row16_one, Move.apply, hw]

/-- Every finite one-run with a supplied zero delimiter terminates in
exactly `n+1` transitions, with no event and no tape modifications. -/
theorem scan16 (n : Nat) (h : Int) (tape : Int → Bool)
    (ht : Holds tape h (List.replicate n true ++ [false])) :
    silentSegment machine (cfg 16 h tape) (cfg 12 (h + n + 1) tape) (n+1) := by
  induction n generalizing h with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Holds] at ht
    simpa using oneSeg machine _ _ (step16_zero h tape ht.1)
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, Holds] at ht
    have hs := oneSeg machine _ _ (step16_one h tape ht.1)
    have hr := ih (h+1) ht.2
    have hall := segAdd machine _ _ _ 1 (n+1) hs hr
    simpa [Int.add_assoc, Int.add_comm, Int.add_left_comm, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hall

/-- A blank right tail supplies a finite bound even when the location of
the first zero is not given. -/
theorem scan16_tail (k : Nat) (h : Int) (tape : Int → Bool)
    (hz : ∀ p ≥ h + (k : Int), tape p = false) :
    ∃ m : Nat, 0 < m ∧ m ≤ k+1 ∧
      silentSegment machine (cfg 16 h tape) (cfg 12 (h + m) tape) m := by
  exact PhysicalOnesScan.tail machine 16 12 step16_one step16_zero k h tape hz

/-- On the actual blank-start run, finite tape support ensures that every
visit to state 16 reaches state 12 in positive finite silent time. -/
theorem reachable_16_to_12 (time : Nat) (hstate : (machine.system.run time).state = 16) :
    ∃ (m : Nat) (e : Config 284), 0 < m ∧ e.state = 12 ∧
      silentSegment machine (machine.system.run time) e m := by
  obtain ⟨b, hb⟩ := run_has_right_zero time
  let h := (machine.system.run time).head
  let k := (max b h-h).toNat
  have hk : b ≤ h+(k : Int) := by
    have hn : 0 ≤ max b h-h := by omega
    have he : (k : Int)=max b h-h := Int.toNat_of_nonneg hn
    omega
  have hz : ∀ p ≥ h+(k : Int), (machine.system.run time).tape p=false := by
    intro p hp
    exact hb p (le_trans hk hp)
  obtain ⟨m, hm, _, hseg⟩ := scan16_tail k h (machine.system.run time).tape hz
  have hcfg : machine.system.run time = cfg 16 h (machine.system.run time).tape := by
    cases hc : machine.system.run time with
    | mk state head tape =>
      simp only [hc,cfg] at hstate ⊢
      simp only [h,hc,cfg] at *
      cases hstate
      rfl
  exact ⟨m, cfg 12 (h+m) (machine.system.run time).tape, hm, rfl, by rw [hcfg]; exact hseg⟩

/-- The state-261 one branch clears its marker, then traverses the given
one-run and its zero delimiter, without events or changes elsewhere. -/
theorem dispatch261_scan16 (n : Nat) (h : Int) (tape : Int → Bool)
    (ht : tape h = true)
    (hs : Holds tape (h+1) (List.replicate n true ++ [false])) :
    silentSegment machine (cfg 261 h tape)
      (cfg 12 (h+1+n+1) (clearAt h tape)) (n+2) := by
  have hscan := scan16 n (h+1) (clearAt h tape)
    (holds_clear_left tape h (h+1) _ (by omega) hs)
  have hstep := oneSeg machine _ _ (step261_one h tape ht)
  have hall := segAdd machine _ _ _ 1 (n+1) hstep hscan
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

/-- On the actual run, the state-261 one-branch has a finite silent
continuation to state 12, without assuming a delimiter as an extra premise. -/
theorem reachable_261_one_to_12 (time : Nat)
    (hstate : (machine.system.run time).state = 261)
    (hone : (machine.system.run time).tape (machine.system.run time).head = true) :
    ∃ (m : Nat) (e : Config 284), 0 < m ∧ e.state = 12 ∧
      silentSegment machine (machine.system.run time) e m := by
  obtain ⟨b, hb⟩ := run_has_right_zero time
  let h := (machine.system.run time).head
  let tape := (machine.system.run time).tape
  let k := (max b (h+1) - (h+1)).toNat
  have hk : b ≤ h+1+(k : Int) := by
    have hn : 0 ≤ max b (h+1)-(h+1) := by omega
    have he : (k : Int)=max b (h+1)-(h+1) := Int.toNat_of_nonneg hn
    omega
  have hz : ∀ p ≥ (h+1)+(k : Int), clearAt h tape p = false := by
    intro p hp
    have hne : p ≠ h := by omega
    have ht : tape p = false := hb p (le_trans hk hp)
    simp [clearAt, hne, ht]
  obtain ⟨m, hm, _, hseg⟩ := scan16_tail k (h+1) (clearAt h tape) hz
  have hcfg : machine.system.run time = cfg 261 h tape := by
    cases hc : machine.system.run time with
    | mk state head cells =>
      simp only [hc,cfg] at hstate ⊢
      simp only [h,tape,hc,cfg] at *
      cases hstate
      rfl
  have hstep := oneSeg machine _ _ (step261_one h tape hone)
  refine ⟨1+m, cfg 12 (h+1+m) (clearAt h tape), by omega, rfl, ?_⟩
  rw [hcfg]
  exact segAdd machine _ _ _ 1 m hstep hseg

end Shared.Beeping.NPcoNP.NativeHalfState16Progress

#print axioms Shared.Beeping.NPcoNP.NativeHalfState16Progress.scan16
#print axioms Shared.Beeping.NPcoNP.NativeHalfState16Progress.dispatch261_scan16
#print axioms Shared.Beeping.NPcoNP.NativeHalfState16Progress.reachable_16_to_12
#print axioms Shared.Beeping.NPcoNP.NativeHalfState16Progress.reachable_261_one_to_12
