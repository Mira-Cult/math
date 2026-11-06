import Shared.Beeping.NPcoNP.NativeHalfReachableMarker
import Shared.Beeping.NPcoNP.NativeHalfSweep

/-! State 28 erases successive ones to its right and exits on the first zero.
Finite support yields such a zero on every actual finite blank-start run.
This is a progress lemma for that physical segment, not a proof of reachability
of state 28 or of correctness of the surrounding HALF routine. -/

namespace Shared.Beeping.NPcoNP.NativeHalfState28Progress

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfReachableMarker

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem row28_zero : machine.table.row 28 false = ⟨false, .left, 6, false⟩ := by decide
theorem row28_one : machine.table.row 28 true = ⟨false, .right, 28, false⟩ := by decide

theorem step28_zero (h : Int) (t : Int → Bool) (ht : t h = false) :
    machine.step (cfg 28 h t) = (cfg 6 (h-1) t, false) := by
  have hw : (⟨28, h, t⟩ : Config 284).write false = t := by
    rw [← ht]
    exact write_current _
  simp [cfg, Machine.step, ht, row28_zero, Move.apply, hw]

theorem step28_one (h : Int) (t : Int → Bool) (ht : t h = true) :
    machine.step (cfg 28 h t) = (cfg 28 (h+1) (put t h false), false) := by
  change machine.step ⟨28, h, t⟩ = (⟨28, h+1, put t h false⟩, false)
  have hw : (⟨28, h, t⟩ : Config 284).write false = put t h false := rfl
  simp [Machine.step, ht, row28_one, Move.apply, hw]

/-- A known zero at distance `k` gives an exit within `k+1` steps, including
the zero-at-head case. The end tape is existentially quantified. -/
theorem scan_to_zero (k : Nat) (h : Int) (t : Int → Bool)
    (hz : t (h + (k : Int)) = false) :
    ∃ (n : Nat) (e : Config 284), 0 < n ∧ n ≤ k+1 ∧ e.state = 6 ∧
      silentSegment machine (cfg 28 h t) e n := by
  induction k generalizing h t with
  | zero =>
    refine ⟨1, cfg 6 (h-1) t, by omega, by omega, rfl, ?_⟩
    exact oneSeg machine _ _ (step28_zero h t (by simpa using hz))
  | succ k ih =>
    cases hv : t h with
    | false =>
      refine ⟨1, cfg 6 (h-1) t, by omega, by omega, rfl, ?_⟩
      exact oneSeg machine _ _ (step28_zero h t hv)
    | true =>
      have hneq : h+1+(k : Int) ≠ h := by omega
      have he : h+1+(k : Int) = h+((Nat.succ k : Nat) : Int) := by push_cast; omega
      have hz' : put t h false ((h+1)+(k : Int)) = false := by
        rw [put_other _ _ _ _ hneq, he]
        exact hz
      obtain ⟨n, e, hn, hb, he, hs⟩ := ih (h+1) (put t h false) hz'
      refine ⟨1+n, e, by omega, by omega, he, ?_⟩
      exact segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step28_one h t hv)) hs

/-- Every finite set of integer tape positions has a strict upper bound. -/
theorem list_has_right_bound (xs : List Int) : ∃ b : Int, ∀ i, b ≤ i → i ∉ xs := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons a xs ih =>
    obtain ⟨b, hb⟩ := ih
    refine ⟨max b (a+1), ?_⟩
    intro i hi
    have h1 : b ≤ i := le_trans (le_max_left _ _) hi
    have h2 : a+1 ≤ i := le_trans (le_max_right _ _) hi
    have hne : i ≠ a := by omega
    simp [hne, hb i h1]

theorem run_has_right_zero (time : Nat) :
    ∃ b : Int, ∀ i, b ≤ i → (machine.system.run time).tape i = false := by
  obtain ⟨touched, htouched⟩ := machine.run_finite_support time
  obtain ⟨b, hb⟩ := list_has_right_bound touched
  refine ⟨b, ?_⟩
  intro i hi
  have ht := htouched i (hb i hi)
  simpa [machine_starts_zero.2.1] using ht

/-- Any actual finite-time state-28 visit finishes this literal scan silently. -/
theorem reachable_28_to_6 (time : Nat)
    (hstate : (machine.system.run time).state = 28) :
    ∃ (n : Nat) (e : Config 284), 0 < n ∧ e.state = 6 ∧
      silentSegment machine (machine.system.run time) e n := by
  obtain ⟨b, hb⟩ := run_has_right_zero time
  let h := (machine.system.run time).head
  let k := (max b h - h).toNat
  have hk : b ≤ h + (k : Int) := by
    have hn : 0 ≤ max b h - h := by omega
    have ht : (k : Int) = max b h - h := Int.toNat_of_nonneg hn
    omega
  have hz : (machine.system.run time).tape (h + (k : Int)) = false := hb _ hk
  obtain ⟨n, e, hn, _, he, hs⟩ := scan_to_zero k h (machine.system.run time).tape hz
  refine ⟨n, e, hn, he, ?_⟩
  have hc : machine.system.run time = cfg 28 h (machine.system.run time).tape := by
    cases hx : machine.system.run time with
    | mk state head tape =>
      simp only [hx, cfg] at hstate ⊢
      simp only [h, hx, cfg] at *
      cases hstate
      rfl
  rw [hc]
  exact hs

/-- A state-23 visit with a rightward marker reaches state 6 in positive
finite silent time. The marker remains an explicit assumption. -/
theorem reachable_marker_to_6 (time : Nat)
    (hstate : (machine.system.run time).state = 23)
    (p : Int) (hpos : (machine.system.run time).head ≤ p)
    (hone : (machine.system.run time).tape p = true) :
    ∃ (n : Nat) (e : Config 284), 0 < n ∧ e.state = 6 ∧
      silentSegment machine (machine.system.run time) e n := by
  obtain ⟨a, c, ha, hc, hs⟩ := reachable_marker_to_28 time hstate p hpos hone
  have hrun : machine.system.run (time+a) = c := by
    rw [EventSystem.run_add, ← PASoundness.ScalarWordRefinement.advance_ofBeep]
    exact hs.1
  have hstate' : (machine.system.run (time+a)).state = 28 := by rw [hrun]; exact hc
  obtain ⟨b, e, hb, he, hs'⟩ := reachable_28_to_6 (time+a) hstate'
  refine ⟨a+b, e, by omega, he, ?_⟩
  apply segAdd machine _ _ _ a b hs
  rw [← hrun]
  exact hs'

end Shared.Beeping.NPcoNP.NativeHalfState28Progress
