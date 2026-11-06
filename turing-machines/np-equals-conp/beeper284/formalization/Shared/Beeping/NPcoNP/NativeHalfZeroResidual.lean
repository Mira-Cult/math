import Shared.Beeping.NPcoNP.NativeHalfCyclePrelude

/-! The literal size-zero residual dispatch from a supplied tape boundary.
No blank-start reachability, cleanup, or complete HALF correctness is claimed. -/
namespace Shared.Beeping.NPcoNP.NativeHalfZeroResidual
open Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfCyclePrelude

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem row40_zero : machine.table.row 40 false = ⟨false, .left, 49, false⟩ := by decide
theorem row49_one : machine.table.row 49 true = ⟨false, .right, 18, false⟩ := by decide

theorem step40_zero (h : Int) (t : Int → Bool) (ht : t h = false) :
    machine.step (cfg 40 h t) = (cfg 49 (h-1) (put t h false), false) := by
  simp [Machine.step, cfg, ht, row40_zero, Move.apply]
  rfl

theorem step49_one (h : Int) (t : Int → Bool) (ht : t h = true) :
    machine.step (cfg 49 h t) = (cfg 18 (h+1) (put t h false), false) := by
  simp [Machine.step, cfg, ht, row49_one, Move.apply]
  rfl

/-- On two supplied consecutive zero cells, the first-cell write is undone
and the second cell remains zero. Exactly three table transitions are silent. -/
theorem zero_residual (h : Int) (t : Int → Bool)
    (h0 : t h = false) (h1 : t (h+1) = false) :
    silentSegment machine (cfg 30 h t) (cfg 18 (h+1) t) 3 := by
  have h1' : put t h true (h+1) = false := by
    rw [put_other _ _ _ _ (by omega)]
    exact h1
  have h0' : put (put t h true) (h+1) false h = true := by
    rw [put_other _ _ _ _ (by omega)]
    simp [put]
  have heq : put (put (put t h true) (h+1) false) h false = t := by
    funext p
    by_cases hp : p = h
    · subst p
      simp [put, h0]
    by_cases hp1 : p = h+1
    · subst p
      simp [put, hp, h1]
    · simp [put, hp, hp1]
  have s0 := oneSeg machine _ _ (step30 h t h0)
  have s1 := oneSeg machine _ _ (step40_zero (h+1) (put t h true) h1')
  have s2 := oneSeg machine _ _ (step49_one h (put (put t h true) (h+1) false) h0')
  have s01 := segAdd machine _ _ _ 1 1 s0 s1
  have s012 := segAdd machine _ _ _ 2 1 (by simpa using s01)
    (by simpa using s2)
  simpa [heq] using s012
end Shared.Beeping.NPcoNP.NativeHalfZeroResidual
