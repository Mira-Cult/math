import Shared.PNP.Record285.DecrementZeroExact

/-! Exact zero-case scanner execution, including its full unchanged bank. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.DecrementZeroExact
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.BootstrapChecker (silent_compose)
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementReturn (atLeftWord completeBits completeCost completeRight)
open Shared.PNP.Record285.IncrementMeaning (foldRuns)
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
attribute [local irreducible] Record285.machine

theorem zero_to_break_exact (gap : Nat) (before : List Nat) (head : Int) (farLeft suffix : Nat) :
    silent Record285.machine (IncrementSelector.cost (gap::before)+4)
      ⟨DecrementSelector.state 0,head,
        DecrementSelector.leftAfter (gap::before) (2*farLeft),true,2*suffix⟩ =
      some (atLeftWord DecrementZero.breakOne
        (head-1-(IncrementSelector.cost (gap::before)+1:Nat)) farLeft
        (4*IncrementSelector.blocksBits (gap::(before++[0])) suffix)) := by
  let runs := 0::foldRuns before []
  let n := IncrementSelector.cost (gap::before)
  let word := DecrementSelector.leftAfter (gap::before) (2*farLeft)
  have hz := DecrementZero.zero_entry Record285.machine (DecrementSelector.state 0)
    DecrementZero.probe DecrementZero.scan DecrementZero.literal_branch_rows head word suffix
  have hs := IncrementReturn.scan_complete Record285.machine DecrementZero.scan
    DecrementZero.check DecrementZero.breakOne DecrementZero.literal_scan_rows
    runs gap (head-1) farLeft (4*suffix+1)
  have hl : word = completeBits runs gap farLeft := return_layout_exact gap before farLeft
  have hc : completeCost runs gap = n+1 := return_cost_exact gap before
  have hout : completeRight runs gap (4*suffix+1) =
      4*IncrementSelector.blocksBits (gap::(before++[0])) suffix :=
    return_output_exact gap before suffix
  rw [← hl,hc,hout] at hs
  have h := silent_compose Record285.machine _ _ _ 3 (n+1) hz hs
  have htime : 3+(n+1) = n+4 := by omega
  simpa only [htime] using h

/-- From a clean terminal, a zero decrement reaches the one-level break
state at the original control boundary with the bank unchanged. -/
theorem terminal_zero_to_break_exact (code : List Bool) (gap : Nat) (before : List Nat)
    (hwalk : walk 162 code = some (.dec before.length)) (head : Int) (leftTail suffix : Nat) :
    let left := bits (pathLeft code) leftTail
    let blocks := gap::before
    let steps := (2*gap+5)+pathCost code+2*IncrementSelector.cost blocks+4
    silent Record285.machine steps
      ⟨decTerminal before.length,head,left,false,
        2*runPattern false gap true (2*IncrementSelector.blocksBits (before++[0]) suffix)⟩ =
      some (atLeftWord DecrementZero.breakOne (head-1) left
        (4*IncrementSelector.blocksBits (gap::(before++[0])) suffix)) := by
  dsimp only
  let left := bits (pathLeft code) leftTail
  let blocks := gap::before
  let n := IncrementSelector.cost blocks
  have ht := DecrementDispatch.terminal_to_target code gap 0 before hwalk head leftTail suffix
  simp only [runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add] at ht
  have hz := zero_to_break_exact gap before (head+1+n) left suffix
  have hh : head+1+(n:Int)-1-(n+1:Nat) = head-1 := by omega
  rw [hh] at hz
  have h := silent_compose Record285.machine _ _ _ ((2*gap+5)+pathCost code+n) (n+4) ht hz
  have htime : ((2*gap+5)+pathCost code+n)+(n+4) =
      (2*gap+5)+pathCost code+2*n+4 := by omega
  simpa only [htime] using h

end Shared.PNP.Record285.DecrementZeroExact
