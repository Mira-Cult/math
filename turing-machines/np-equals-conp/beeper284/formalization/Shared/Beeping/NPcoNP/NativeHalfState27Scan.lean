import Shared.Beeping.NPcoNP.NativeHalfSweep

/-! The literal state-27 rightward scan over a finite run of zeroes.
The tape pattern is a supplied premise.  This does not prove that the
selected machine reaches it or that the complete HALF primitive returns. -/

namespace Shared.Beeping.NPcoNP.NativeHalfState27Scan
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfRows

theorem row27_zero : machine.table.row 27 false = ⟨false, .right, 27, false⟩ := by decide
theorem row27_one : machine.table.row 27 true = ⟨false, .right, 28, false⟩ := by decide

theorem step27_zero (h : Int) (t : Int → Bool) (ht : t h = false) :
    machine.step (cfg 27 h t) = (cfg 27 (h+1) t, false) := by
  have hw : (⟨27, h, t⟩ : Config 284).write false = t := by rw [← ht]; exact write_current _
  simp [cfg, Machine.step, ht, row27_zero, Move.apply, hw]

theorem step27_one (h : Int) (t : Int → Bool) (ht : t h = true) :
    machine.step (cfg 27 h t) = (cfg 28 (h+1) (put t h false), false) := by
  change machine.step ⟨27, h, t⟩ = (⟨28, h+1, put t h false⟩, false)
  have hw : (⟨27, h, t⟩ : Config 284).write false = put t h false := rfl
  simp [Machine.step, ht, row27_one, Move.apply, hw]

/-- Scan exactly `k` supplied zero cells without changing any tape cell. -/
theorem scan_zeroes (h : Int) (t : Int → Bool) (k : Nat)
    (hz : ∀ i : Nat, i < k → t (h + (i : Int)) = false) :
    silentSegment machine (cfg 27 h t) (cfg 27 (h + k) t) k := by
  induction k generalizing h with
  | zero => simp [silentSegment, WordEventSystem.advance, WordEventSystem.wordFrom]
  | succ k ih =>
    have h0 : t h = false := by simpa using hz 0 (by omega)
    have htail : ∀ i : Nat, i < k → t ((h+1) + (i : Int)) = false := by
      intro i hi
      have hh := hz (i+1) (by omega)
      simpa [Nat.cast_add, Int.add_assoc, Int.add_comm, Int.add_left_comm] using hh
    have hs := oneSeg machine _ _ (step27_zero h t h0)
    have ht := ih (h+1) htail
    have hc := segAdd machine _ _ _ 1 k hs ht
    simpa [Nat.cast_add, Nat.add_comm, Int.add_assoc, Int.add_comm, Int.add_left_comm] using hc

/-- The first one is consumed after the zero scan; all other cells are
preserved by the explicit `put` update. -/
theorem scan_to_one (h : Int) (t : Int → Bool) (k : Nat)
    (hz : ∀ i : Nat, i < k → t (h + (i : Int)) = false)
    (ho : t (h + k) = true) :
    silentSegment machine (cfg 27 h t)
      (cfg 28 (h + k + 1) (put t (h + k) false)) (k+1) := by
  exact segAdd machine _ _ _ k 1 (scan_zeroes h t k hz)
    (oneSeg machine _ _ (step27_one (h+k) t ho))

theorem scan_to_one_positive (k : Nat) : 0 < k+1 := by omega

theorem scan_to_one_no_beep (h : Int) (t : Int → Bool) (k : Nat)
    (hz : ∀ i : Nat, i < k → t (h + (i : Int)) = false)
    (ho : t (h + k) = true) (j : Nat) (hj : j < k+1) :
    ¬ machine.system.BeepFrom (cfg 27 h t) j :=
  silent_no_beep machine _ _ _ j (scan_to_one h t k hz ho) hj

end Shared.Beeping.NPcoNP.NativeHalfState27Scan
