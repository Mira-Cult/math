import Shared.PNP.Record285.DecrementZeroComposition

/-! Exact return-scanner witnesses and bank reconstruction for a zero field. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.DecrementZeroExact
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementReturn (atLeftWord completeBits completeCost completeRight)
open Shared.PNP.Record285.IncrementMeaning (foldRuns backFold)
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
attribute [local irreducible] Record285.machine

theorem selector_left_exact (blocks runs : List Nat) (last farLeft : Nat) :
    DecrementSelector.leftAfter blocks (1+2*completeBits runs last farLeft) =
      2*(1+2*completeBits (foldRuns blocks runs) last farLeft) := by
  induction blocks generalizing runs with
  | nil => rfl
  | cons k ks ih =>
    simp only [DecrementSelector.leftAfter,IncrementReturn.push_field_layout,foldRuns]
    exact ih (k::runs)

theorem return_layout_exact (gap : Nat) (before : List Nat) (farLeft : Nat) :
    DecrementSelector.leftAfter (gap::before) (2*farLeft) =
      completeBits (0::foldRuns before []) gap farLeft := by
  have hfirst : pushBit (gap+1) true (2*(2*farLeft)) =
      1+2*completeBits [] gap farLeft := by
    rw [IncrementReturn.push_run]
    simp only [runPattern,completeBits,bitVal,if_true]
  change DecrementSelector.leftAfter before (pushBit (gap+1) true (2*(2*farLeft))) = _
  rw [hfirst,selector_left_exact]
  simp only [completeBits,runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]

theorem return_cost_exact (gap : Nat) (before : List Nat) :
    completeCost (0::foldRuns before []) gap = IncrementSelector.cost (gap::before)+1 := by
  simp only [completeCost,IncrementMeaning.folded_cost,IncrementMeaning.fieldCost,
    IncrementMeaning.selector_cost]
  omega

theorem return_output_exact (gap : Nat) (before : List Nat) (suffix : Nat) :
    completeRight (0::foldRuns before []) gap (4*suffix+1) =
      4*IncrementSelector.blocksBits (gap::(before++[0])) suffix := by
  rw [show 4*suffix+1 = 2*(2*suffix)+1 by omega,IncrementMeaning.scan_output]
  simp only [backFold,pushBit,bitVal,if_true]
  rw [show 2*(2*(2*suffix)+1) = 2*(4*suffix+1) by omega,
    IncrementMeaning.backFold_foldRuns]
  simp only [backFold]
  change 4*pushBit (gap+1) true (2*IncrementSelector.blocksBits before (4*suffix+1)) = _
  have hz : 4*suffix+1 = IncrementSelector.blocksBits [0] suffix := by
    simp [IncrementSelector.blocksBits,runPattern,bitVal]; omega
  rw [hz,← IncrementMeaning.blocks_append,← IncrementMeaning.blocks_cons]

end Shared.PNP.Record285.DecrementZeroExact
