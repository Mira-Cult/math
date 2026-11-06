import Shared.Beeping.NPcoNP.NativeHalfReturn23

/-! A state-23 return scan cannot silently stall on a tape with a zero tail
to the left. In particular every *reachable finite-time* blank-start tape has
such a tail. This does not claim that state 23 is reached, identify the bank,
or establish any subsequent selector or complete-HALF behavior. -/

namespace Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport

open Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfReturn23

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- A left-zero tail forces either scanner phase to finish in at most `k+2`
transitions, with unchanged tape and no beeps. -/
theorem scan_left_zero (k : Nat) (h : Int) (t : Int → Bool)
    (hz : ∀ p ≤ h - (k : Int), t p = false) :
    ∀ (phase : Bool), ∃ (n : Nat) (endHead : Int), 0 < n ∧ n ≤ k + 2 ∧
      silentSegment machine (cfg (if phase then 24 else 23) h t)
        (cfg 1 endHead t) n := by
  induction k generalizing h with
  | zero =>
    intro phase
    have h0 : t h = false := hz h (by simp)
    have h1 : t (h-1) = false := hz (h-1) (by simp)
    cases phase with
    | false =>
      refine ⟨2, h-2, by omega, by omega, ?_⟩
      have ha := oneSeg machine _ _ (step23_zero h t h0)
      have hb := oneSeg machine _ _ (step24_zero (h-1) t h1)
      have he : h - 1 - 1 = h - 2 := by omega
      simpa [he] using segAdd machine _ _ _ 1 1 ha hb
    | true =>
      refine ⟨1, h-1, by omega, by omega, ?_⟩
      simpa using oneSeg machine _ _ (step24_zero h t h0)
  | succ k ih =>
    intro phase
    have hz' : ∀ p ≤ (h-1) - (k : Int), t p = false := by
      intro p hp
      apply hz p
      simp only [Nat.cast_succ] at *
      omega
    cases phase with
    | false =>
      cases hv : t h with
      | false =>
        obtain ⟨n, hp, hn, bound, hs⟩ := ih (h-1) hz' true
        refine ⟨1+n, hp, by omega, by omega, ?_⟩
        have ha := oneSeg machine _ _ (step23_zero h t hv)
        simpa using segAdd machine _ _ _ 1 n ha hs
      | true =>
        obtain ⟨n, hp, hn, bound, hs⟩ := ih (h-1) hz' false
        refine ⟨1+n, hp, by omega, by omega, ?_⟩
        have ha := oneSeg machine _ _ (step23_one h t hv)
        simpa using segAdd machine _ _ _ 1 n ha hs
    | true =>
      cases hv : t h with
      | false =>
        refine ⟨1, h-1, by omega, by omega, ?_⟩
        simpa using oneSeg machine _ _ (step24_zero h t hv)
      | true =>
        obtain ⟨n, hp, hn, bound, hs⟩ := ih (h-1) hz' false
        refine ⟨1+n, hp, by omega, by omega, ?_⟩
        have ha := oneSeg machine _ _ (step24_one h t hv)
        simpa using segAdd machine _ _ _ 1 n ha hs

/-- Every finite set of integer cells has a lower bound outside it. -/
theorem list_has_left_bound (xs : List Int) : ∃ b : Int, ∀ i, i ≤ b → i ∉ xs := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons a xs ih =>
    obtain ⟨b, hb⟩ := ih
    refine ⟨min b (a - 1), ?_⟩
    intro i hi
    have h1 : i ≤ b := le_trans hi (min_le_left _ _)
    have h2 : i ≤ a - 1 := le_trans hi (min_le_right _ _)
    have hne : i ≠ a := by omega
    simp [hne, hb i h1]

/-- A finite-time execution from the actual all-zero blank tape has a
left-zero tail, irrespective of its current state. -/
theorem run_has_left_zero (time : Nat) :
    ∃ b : Int, ∀ i, i ≤ b → (machine.system.run time).tape i = false := by
  obtain ⟨touched, htouched⟩ := machine.run_finite_support time
  obtain ⟨b, hb⟩ := list_has_left_bound touched
  refine ⟨b, ?_⟩
  intro i hi
  have ht := htouched i (hb i hi)
  simpa [machine_starts_zero.2.1] using ht

/-- If the actual blank-start run ever reaches scanner state 23, it takes a
positive finite silent segment to state 1 with its tape unchanged. This is a
conditional progress theorem, not a proof that state 23 is reached. -/
theorem reachable_23_progress (time : Nat)
    (hstate : (machine.system.run time).state = 23) :
    ∃ (n : Nat) (endHead : Int), 0 < n ∧
      silentSegment machine (machine.system.run time)
        (cfg 1 endHead (machine.system.run time).tape) n := by
  obtain ⟨b, hb⟩ := run_has_left_zero time
  let h := (machine.system.run time).head
  let k := (h - min b h).toNat
  have hk : h - (k : Int) ≤ b := by
    have hn : 0 ≤ h - min b h := by omega
    have ht : (k : Int) = h - min b h := by
      dsimp [k]
      exact Int.toNat_of_nonneg hn
    omega
  have hz : ∀ p ≤ h - (k : Int), (machine.system.run time).tape p = false := by
    intro p hp
    exact hb p (le_trans hp hk)
  obtain ⟨n, endHead, hn, _, hs⟩ := scan_left_zero k h (machine.system.run time).tape hz false
  refine ⟨n, endHead, hn, ?_⟩
  have he : machine.system.run time = cfg 23 h (machine.system.run time).tape := by
    cases hc : machine.system.run time with
    | mk state head tape =>
      simp only [hc, cfg] at hstate ⊢
      simp only [h, hc, cfg] at *
      cases hstate
      rfl
  change silentSegment machine (cfg 23 h (machine.system.run time).tape)
    (cfg 1 endHead (machine.system.run time).tape) n at hs
  rw [he]
  exact hs

end Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport
