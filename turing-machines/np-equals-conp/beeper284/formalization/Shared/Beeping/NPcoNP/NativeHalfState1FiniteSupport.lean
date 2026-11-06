import Shared.Beeping.NPcoNP.NativeHalfState1Scan
import Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport

/-! The literal state-1 carry scan cannot silently stall on a finite-time
blank-start tape: a zero exists to the left. This is conditional on reaching
state 1; no claim is made about reaching that state or subsequent behavior. -/

namespace Shared.Beeping.NPcoNP.NativeHalfState1FiniteSupport

open Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- A zero `k` cells left guarantees a first zero within that distance, with
all cells between the head and that zero equal to one. -/
theorem first_zero (k : Nat) (h : Int) (t : Int → Bool)
    (hz : t (h - (k : Int)) = false) :
    ∃ j ≤ k, downHolds t h (List.replicate j true ++ [false]) := by
  induction k generalizing h with
  | zero =>
    refine ⟨0, by omega, ?_⟩
    simpa [downHolds] using hz
  | succ k ih =>
    cases hh : t h with
    | false =>
      refine ⟨0, by omega, ?_⟩
      simpa [downHolds] using hh
    | true =>
      have hp : (h-1) - (k : Int) = h - ((k+1 : Nat) : Int) := by omega
      have hz' : t ((h-1) - (k : Int)) = false := by simpa [hp] using hz
      obtain ⟨j, hj, hm⟩ := ih (h-1) hz'
      refine ⟨j+1, by omega, ?_⟩
      simpa [List.replicate_succ, downHolds, hh] using hm

/-- From every actual blank-start configuration in state 1 the table reaches
state 27 in a positive finite silent segment. The resulting tape is exactly
the carry scan's specified `result`. -/
theorem reachable_1_progress (time : Nat)
    (hstate : (machine.system.run time).state = 1) :
    ∃ (j : Nat),
      silentSegment machine (machine.system.run time)
        (cfg 27 ((machine.system.run time).head - (j : Int) + 1)
          (result (machine.system.run time).tape (machine.system.run time).head j))
        (j+1) := by
  obtain ⟨b, hb⟩ := run_has_left_zero time
  let h := (machine.system.run time).head
  let k := (h - min b h).toNat
  have hk : h - (k : Int) ≤ b := by
    have hn : 0 ≤ h - min b h := by omega
    have ht : (k : Int) = h - min b h := by
      dsimp [k]
      exact Int.toNat_of_nonneg hn
    omega
  have hz : (machine.system.run time).tape (h - (k : Int)) = false := hb _ hk
  obtain ⟨j, _, hm⟩ := first_zero k h (machine.system.run time).tape hz
  refine ⟨j, ?_⟩
  have hs := scan (machine.system.run time).tape h j hm
  have he : machine.system.run time = cfg 1 h (machine.system.run time).tape := by
    cases hc : machine.system.run time with
    | mk state head tape =>
      simp only [hc, cfg] at hstate ⊢
      simp only [h, hc, cfg] at *
      cases hstate
      rfl
  rw [he]
  exact hs

end Shared.Beeping.NPcoNP.NativeHalfState1FiniteSupport
