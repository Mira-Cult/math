import Shared.PNP.Record285.DecrementNonzeroShiftRun

/-! Exact nonzero decrement shift and scanner return, preserving all tape. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.DecrementNonzeroReturn
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.BootstrapChecker (silent_compose)
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementShift (atWord suffixBits)
open Shared.PNP.Record285.IncrementReturn (atLeftWord completeBits completeCost completeRight)
open Shared.PNP.Record285.IncrementMeaning (foldRuns backFold)
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
attribute [local irreducible] Record285.machine

theorem selected_left_exact (gap : Nat) (before : List Nat) (far : Nat) :
    DecrementSelector.leftAfter (gap::before) (2*far) =
      2*(1+2*completeBits (foldRuns before []) gap far) := by
  have hfirst : pushBit (gap+1) true (2*(2*far)) =
      1+2*completeBits [] gap far := by
    rw [IncrementReturn.push_run]
    simp only [runPattern,completeBits,bitVal,if_true]
  change DecrementSelector.leftAfter before (pushBit (gap+1) true (2*(2*far))) = _
  rw [hfirst,DecrementZeroExact.selector_left_exact]

theorem scan_cost_exact (fields : List Nat) (k : Nat) :
    completeCost (foldRuns fields []) k = DecrementNonzeroScan.scanCost k fields := by
  simp only [IncrementMeaning.folded_cost,completeCost,DecrementNonzeroScan.scanCost,
    IncrementMeaning.shift_cost]
  omega

theorem return_cost_exact (gap : Nat) (before : List Nat) :
    1+completeCost (foldRuns before []) gap = IncrementSelector.cost (gap::before) := by
  simp only [IncrementMeaning.folded_cost,completeCost,IncrementMeaning.selector_cost,
    IncrementMeaning.fieldCost]
  omega

/-- The reverse scanner reconstructs all fields, decrements the target, and
preserves the arbitrary retained suffix after an extra zero field. -/
theorem return_output_exact (gap k : Nat) (before fields : List Nat) (retained : Nat) :
    completeRight (foldRuns before []) gap
      (2*(2*IncrementSelector.blocksBits (k::fields) (4*retained+1))+1) =
    4*IncrementSelector.blocksBits (gap::(before++[k]++fields++[0])) retained := by
  rw [IncrementMeaning.scan_output,IncrementMeaning.backFold_foldRuns]
  simp only [backFold,← IncrementMeaning.blocks_cons,← IncrementMeaning.blocks_append]
  have hz : 4*retained+1 = IncrementSelector.blocksBits [0] retained := by
    simp [IncrementSelector.blocksBits,runPattern,bitVal]; omega
  rw [hz,← IncrementMeaning.blocks_append]
  congr 2
  simp [List.append_assoc]

/-- A positive target reaches the ordinary break state after the complete
leftward shift and return scanner, with the decremented bank reconstructed. -/
theorem terminal_nonzero_to_break (code : List Bool) (gap k : Nat) (before fields : List Nat)
    (hwalk : walk 162 code = some (.dec before.length)) (head : Int) (leftTail retained : Nat) :
    let left := bits (pathLeft code) leftTail
    let blocks := gap::before
    let steps := (2*gap+5)+pathCost code+IncrementSelector.cost blocks+
      (2+DecrementNonzeroScan.scanCost k fields)+
      (2+completeCost (foldRuns fields []) k)+
      (1+completeCost (foldRuns before []) gap)
    silent Record285.machine steps
      ⟨decTerminal before.length,head,left,false,
        2*runPattern false gap true
          (2*IncrementSelector.blocksBits (before++[k+1]) (suffixBits fields retained))⟩ =
      some (atLeftWord IncrementReturn.breakState (head-1) left
        (4*IncrementSelector.blocksBits (gap::(before++[k]++fields++[0])) retained)) := by
  dsimp only
  let left := bits (pathLeft code) leftTail
  let blocks := gap::before
  let targetHead := head+1+IncrementSelector.cost blocks
  let middle := 1+2*completeBits (foldRuns before []) gap left
  let scanLen := DecrementNonzeroScan.scanCost k fields
  let shiftLen := 2+scanLen
  let returnLen := 1+completeCost (foldRuns before []) gap
  have ht := DecrementNonzeroComposition.terminal_nonzero_to_shift code gap k before fields
    hwalk head leftTail retained
  have hl := selected_left_exact gap before left
  dsimp only at ht
  rw [hl] at ht
  have hs := DecrementNonzeroShiftRun.shift_to_return fields k (targetHead+scanLen) middle retained
  have hc := scan_cost_exact fields k
  rw [hc] at hs
  have hhead : targetHead+(scanLen:Int)-2-(scanLen:Int) = targetHead-2 := by omega
  rw [hhead] at hs
  have hr := IncrementMeaning.scan_leading Record285.machine IncrementShift.returnState
    IncrementReturn.checkState IncrementReturn.breakState IncrementReturn.literal_rows
    (foldRuns before []) gap (targetHead-2) left
    (2*IncrementSelector.blocksBits (k::fields) (4*retained+1))
  have hout := return_output_exact gap k before fields retained
  rw [hout] at hr
  have hreturn := return_cost_exact gap before
  have hh : targetHead-2-(1+(completeCost (foldRuns before []) gap:Int)) = head-1 := by
    dsimp [targetHead,blocks]
    omega
  rw [hh] at hr
  have htail := silent_compose Record285.machine _ _ _ shiftLen returnLen hs hr
  have hall := silent_compose Record285.machine _ _ _
    (((2*gap+5)+pathCost code+IncrementSelector.cost blocks)+(2+scanLen))
    (shiftLen+returnLen) ht htail
  have htime : (((2*gap+5)+pathCost code+IncrementSelector.cost blocks)+(2+scanLen))+
      (shiftLen+returnLen) =
      ((2*gap+5)+pathCost code+IncrementSelector.cost blocks)+(2+scanLen)+shiftLen+returnLen := by omega
  simpa only [hc,htime] using hall

end Shared.PNP.Record285.DecrementNonzeroReturn
