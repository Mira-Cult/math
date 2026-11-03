import Shared.PNP.Record285.DecrementBreakCleanup

/-! Compose zero decrement and one-level break with complete cleanup. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.DecrementZeroCleanup
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementReturn (atLeftWord)
open Shared.PNP.Record285.IncrementCleanup (peel peel_bits path_has_zero peel_append)
open Shared.PNP.Record285.IncrementPreparation (dispatch0)
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
attribute [local irreducible] Record285.machine

theorem path_peel_tail_has_zero (code : List Bool) : false ∈ (peel (pathLeft code)).2 := by
  have hz : false ∈ code.reverse++[false,true,true] := by simp
  have h := peel_append (code.reverse++[false,true,true]) (List.replicate 6 false) hz
  have hs : (peel (pathLeft code)).2 =
      (peel (code.reverse++[false,true,true])).2 ++ List.replicate 6 false := by
    simpa only [pathLeft,List.append_assoc] using congrArg Prod.snd h
  rw [hs]
  simp

/-- A clean zero-target decrement completes its one-level break and returns
to the detector dispatcher. Both peeled control suffixes, the whole unary
bank and arbitrary far tapes are represented exactly. -/
theorem terminal_zero_to_dispatch (code : List Bool) (gap : Nat) (before : List Nat)
    (hwalk : walk 162 code = some (.dec before.length)) (head : Int) (leftTail suffix : Nat) :
    let p1 := peel (pathLeft code)
    let p2 := peel p1.2
    let bank := IncrementSelector.blocksBits (before++[0]) suffix
    let far := bits p2.2 leftTail
    let steps := (2*gap+5)+pathCost code+2*IncrementSelector.cost (gap::before)+4+
      (3*(p1.1+p2.1)+2*gap+12)
    silent Record285.machine steps
      ⟨decTerminal before.length,head,bits (pathLeft code) leftTail,false,
        2*runPattern false gap true (2*bank)⟩ =
      some (atLeftWord dispatch0 (head-p1.1-p2.1-3) far
        (1+2*runPattern false (p1.1+p2.1+gap+3) true (2*bank))) := by
  dsimp only
  let p1 := peel (pathLeft code)
  let p2 := peel p1.2
  let bank := IncrementSelector.blocksBits (before++[0]) suffix
  let far := bits p2.2 leftTail
  have hfirst := DecrementZeroExact.terminal_zero_to_break_exact code gap before hwalk head leftTail suffix
  have hw1 := peel_bits (pathLeft code) (path_has_zero code) leftTail
  have hw2 := peel_bits p1.2 (path_peel_tail_has_zero code) leftTail
  change bits (pathLeft code) leftTail = runPattern true p1.1 false (bits p1.2 leftTail) at hw1
  change bits p1.2 leftTail = runPattern true p2.1 false far at hw2
  rw [hw2] at hw1
  have hbank : IncrementSelector.blocksBits (gap::(before++[0])) suffix =
      runPattern true (gap+1) false bank := by
    simp only [IncrementSelector.blocksBits,runPattern,bitVal,if_true,bank]
  rw [hbank] at hfirst
  have hcleanup := DecrementBreakCleanup.skip_and_cleanup p1.1 p2.1 gap head far bank
  rw [← hw1] at hcleanup
  rw [silent_add,hfirst]
  simp only [Option.bind_some]
  exact hcleanup

theorem terminal_zero_to_dispatch_physical (code : List Bool) (gap : Nat) (before : List Nat)
    (hwalk : walk 162 code = some (.dec before.length)) (head : Int) (leftTail suffix : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨decTerminal before.length,head,bits (pathLeft code) leftTail,false,
      2*runPattern false gap true (2*IncrementSelector.blocksBits (before++[0]) suffix)⟩ physical) :
    let p1 := peel (pathLeft code)
    let p2 := peel p1.2
    let bank := IncrementSelector.blocksBits (before++[0]) suffix
    let far := bits p2.2 leftTail
    let steps := (2*gap+5)+pathCost code+2*IncrementSelector.cost (gap::before)+4+
      (3*(p1.1+p2.1)+2*gap+12)
    Rel (atLeftWord dispatch0 (head-p1.1-p2.1-3) far
      (1+2*runPattern false (p1.1+p2.1+gap+3) true (2*bank)))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  have hp := silent_physical Record285.machine _ physical hrel _ _
    (terminal_zero_to_dispatch code gap before hwalk head leftTail suffix)
  exact ⟨hp.1,hp.2,by omega⟩

end Shared.PNP.Record285.DecrementZeroCleanup
