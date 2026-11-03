import Shared.PNP.Record285.DecrementDispatch
import Shared.PNP.Record285.DecrementZero

/-! Complete literal zero-field decrement from the clean terminal through
selection and the zero-case return scanner. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.DecrementZeroComposition
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementReturn (atLeftWord completeCost completeRight)
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar

/-- For any producer decrement path and any preceding fields, a zero
target reaches the one-level break state in finite silent time. -/
theorem terminal_zero_to_break (code : List Bool) (gap : Nat) (before : List Nat)
    (hwalk : walk 162 code = some (.dec before.length)) (head : Int) (leftTail suffix : Nat) :
    ∃ runs last,
      let left := bits (pathLeft code) leftTail
      let blocks := gap::before
      let targetHead := head+1+IncrementSelector.cost blocks
      let steps := (2*gap+5)+pathCost code+IncrementSelector.cost blocks+
        (3+completeCost (0::runs) last)
      silent Record285.machine steps
        ⟨decTerminal before.length,head,left,false,
          2*runPattern false gap true (2*IncrementSelector.blocksBits (before++[0]) suffix)⟩ =
        some (atLeftWord DecrementZero.breakOne
          (targetHead-1-completeCost (0::runs) last) left
          (completeRight (0::runs) last (4*suffix+1))) := by
  let left := bits (pathLeft code) leftTail
  let blocks := gap::before
  let targetHead := head+1+IncrementSelector.cost blocks
  have ht := DecrementDispatch.terminal_to_target code gap 0 before hwalk head leftTail suffix
  simp only [runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add] at ht
  obtain ⟨runs,last,hzero⟩ := DecrementZero.zero_to_break gap before targetHead left suffix
  refine ⟨runs,last,?_⟩
  dsimp only
  rw [silent_add,ht]
  simp only [Option.bind_some]
  exact hzero

theorem terminal_zero_to_break_physical (code : List Bool) (gap : Nat) (before : List Nat)
    (hwalk : walk 162 code = some (.dec before.length)) (head : Int) (leftTail suffix : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨decTerminal before.length,head,bits (pathLeft code) leftTail,false,
      2*runPattern false gap true (2*IncrementSelector.blocksBits (before++[0]) suffix)⟩ physical) :
    ∃ runs last,
      let left := bits (pathLeft code) leftTail
      let blocks := gap::before
      let targetHead := head+1+IncrementSelector.cost blocks
      let steps := (2*gap+5)+pathCost code+IncrementSelector.cost blocks+
        (3+completeCost (0::runs) last)
      Rel (atLeftWord DecrementZero.breakOne (targetHead-1-completeCost (0::runs) last) left
        (completeRight (0::runs) last (4*suffix+1)))
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
      0 < steps := by
  obtain ⟨runs,last,h⟩ := terminal_zero_to_break code gap before hwalk head leftTail suffix
  have hp := silent_physical Record285.machine _ physical hrel _ _ h
  refine ⟨runs,last,hp.1,hp.2,?_⟩
  omega

end Shared.PNP.Record285.DecrementZeroComposition
