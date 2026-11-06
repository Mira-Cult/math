import Shared.Beeping.NPcoNP.NativeHalfSweep

/-! Literal three-transition preparation of one regular HALF cycle. This is
only a local physical fact under supplied tape bits; it does not assert that
the blank-start run reaches the configuration or establish the full HALF. -/
namespace Shared.Beeping.NPcoNP.NativeHalfCyclePrelude
open Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem row30_zero : machine.table.row 30 false = ⟨true, .right, 40, false⟩ := by decide
theorem row40_one : machine.table.row 40 true = ⟨false, .right, 43, false⟩ := by decide
theorem row43_one : machine.table.row 43 true = ⟨false, .right, 32, false⟩ := by decide

theorem step30 (h : Int) (t : Int → Bool) (ht : t h = false) :
    machine.step (cfg 30 h t) = (cfg 40 (h+1) (put t h true), false) := by
  simp [Machine.step, cfg, ht, row30_zero, Move.apply]
  rfl

theorem step40 (h : Int) (t : Int → Bool) (ht : t h = true) :
    machine.step (cfg 40 h t) = (cfg 43 (h+1) (put t h false), false) := by
  simp [Machine.step, cfg, ht, row40_one, Move.apply]
  rfl

theorem step43 (h : Int) (t : Int → Bool) (ht : t h = true) :
    machine.step (cfg 43 h t) = (cfg 32 (h+1) (put t h false), false) := by
  simp [Machine.step, cfg, ht, row43_one, Move.apply]
  rfl

/-- Three paid silent transitions fill the old boundary and open the new
two-zero gap. All other cells are unchanged by the explicit three writes. -/
theorem prelude (h : Int) (t : Int → Bool)
    (h0 : t h = false) (h1 : t (h+1) = true) (h2 : t (h+2) = true) :
    silentSegment machine (cfg 30 h t)
      (cfg 32 (h+3) (put (put (put t h true) (h+1) false) (h+2) false)) 3 := by
  have h1' : put t h true (h+1) = true := by
    rw [put_other _ _ _ _ (by omega)]
    exact h1
  have h2' : put (put t h true) (h+1) false (h+2) = true := by
    rw [put_other _ _ _ _ (by omega), put_other _ _ _ _ (by omega)]
    exact h2
  have s0 := oneSeg machine _ _ (step30 h t h0)
  have s1 := oneSeg machine _ _ (step40 (h+1) (put t h true) h1')
  have s2 := oneSeg machine _ _ (step43 (h+2) (put (put t h true) (h+1) false) h2')
  have h01 := segAdd machine _ _ _ 1 1 s0 s1
  have h012 := segAdd machine _ _ _ 2 1 (by simpa using h01) (by simpa [Int.add_assoc] using s2)
  simpa [Int.add_assoc] using h012

end Shared.Beeping.NPcoNP.NativeHalfCyclePrelude
