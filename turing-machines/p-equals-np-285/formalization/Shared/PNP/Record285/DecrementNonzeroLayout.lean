import Shared.PNP.Record285.DecrementNonzeroShift
import Shared.PNP.Record285.DecrementZeroExact

/-! Exact suffix layout for the nonzero decrement's reverse shift. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.DecrementNonzeroLayout
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementReturn (completeBits)
open Shared.PNP.Record285.IncrementMeaning (foldRuns)
open Shared.PNP.Record285.DecrementNonzeroScan (scannedLeft)
open Shared.PNP.Record285.DecrementNonzeroShift (shiftedRight)

theorem push_ones_cons (k : Nat) (runs : List Nat) (last far : Nat) :
    pushBit k true (1+2*completeBits (0::runs) last far) =
      1+2*completeBits (k::runs) last far := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pushBit,pushBit_affine,ih]
    simp only [completeBits,runPattern,bitVal,if_true]
    omega

theorem push_initial (k far : Nat) :
    pushBit k true (4*(2*far)+1) = 1+2*completeBits [] k far := by
  induction k with
  | zero => simp [pushBit,completeBits,runPattern,bitVal]; omega
  | succ k ih =>
    rw [pushBit,pushBit_affine,ih]
    simp only [completeBits,runPattern,bitVal,if_true]
    omega

theorem scan_layout_aux (fields : List Nat) (k : Nat) (runs : List Nat) (last far : Nat) :
    scannedLeft k fields (1+2*completeBits (0::runs) last far) =
      1+2*completeBits (foldRuns fields (k::runs)) last far := by
  induction fields generalizing k runs with
  | nil => simpa only [scannedLeft,foldRuns] using push_ones_cons k runs last far
  | cons next rest ih =>
    simp only [scannedLeft,foldRuns]
    rw [push_ones_cons]
    have h : 4*(1+2*completeBits (k::runs) last far)+1 =
        1+2*completeBits (0::k::runs) last far := by
      simp only [completeBits,runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
      omega
    rw [h]
    exact ih next (k::runs)

theorem scan_layout (fields : List Nat) (k far : Nat) :
    scannedLeft k fields (4*(2*far)+1) = 1+2*completeBits (foldRuns fields []) k far := by
  cases fields with
  | nil => simpa only [scannedLeft,foldRuns] using push_initial k far
  | cons next rest =>
    simp only [scannedLeft,foldRuns]
    rw [push_initial]
    have h : 4*(1+2*completeBits [] k far)+1 =
        1+2*completeBits [0] k far := by
      simp only [completeBits,runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
      omega
    rw [h]
    exact scan_layout_aux rest next [] k far

theorem shifted_step (k : Nat) (runs : List Nat) (last right : Nat) :
    shiftedRight (k::runs) last (2*right) =
      shiftedRight runs last (2*IncrementSelector.blocksBits [k] right) := by
  simp only [shiftedRight]
  have hb : 4*pushBit k true (2*right)+2 =
      2*IncrementSelector.blocksBits [k] right := by
    rw [IncrementReturn.push_run]
    simp only [IncrementSelector.blocksBits]
    omega
  rw [hb]

theorem shifted_fold (fields runs : List Nat) (last right : Nat) :
    shiftedRight (foldRuns fields runs) last (2*right) =
      shiftedRight runs last (2*IncrementSelector.blocksBits fields right) := by
  induction fields generalizing runs with
  | nil => rfl
  | cons k ks ih =>
    simp only [foldRuns,ih,shifted_step,IncrementSelector.blocksBits]

/-- The shift reconstructs the decremented target and all later fields,
including the terminating zero and arbitrary retained high suffix. -/
theorem shifted_output (fields : List Nat) (k retained : Nat) :
    shiftedRight (foldRuns fields []) k (8*retained+2) =
      2*IncrementSelector.blocksBits (k::fields) (4*retained+1) := by
  rw [show 8*retained+2 = 2*(4*retained+1) by omega,shifted_fold]
  simp only [shiftedRight]
  rw [IncrementReturn.push_run]
  simp only [IncrementSelector.blocksBits]
  omega

end Shared.PNP.Record285.DecrementNonzeroLayout
