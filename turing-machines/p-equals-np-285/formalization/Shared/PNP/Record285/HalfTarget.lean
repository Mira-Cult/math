import Shared.PNP.Record285.HalfSelector
import Shared.PNP.Record285.GrammarRootDispatch

/-! Complete native-half dispatcher and operand selection. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.HalfDispatch
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar

/-- A clean half path proceeds through preparation, redispatch and all
preceding fields to the selected unary field. The selected field itself is
not modified by this segment. -/
theorem terminal_to_target (code : List Bool) (gap target : Nat) (before : List Nat)
    (hwalk : walk 162 code = some (.half before.length)) (head : Int) (leftTail suffix : Nat) :
    let blocks := gap::before
    let bank := IncrementSelector.blocksBits (before++[target]) suffix
    let steps := (2*gap+5)+pathCost code+IncrementSelector.cost blocks
    silent Record285.machine steps
      ⟨halfTerminal before.length,head,bits (pathLeft code) leftTail,false,
        2*runPattern false gap true (2*bank)⟩ =
      some ⟨HalfSelector.state 0,head+1+IncrementSelector.cost blocks,
        DecrementSelector.leftAfter blocks (2*bits (pathLeft code) leftTail),true,
        runPattern true target false suffix⟩ := by
  dsimp only
  let blocks := gap::before
  let targetTail := IncrementSelector.blocksBits [target] suffix
  let bank := IncrementSelector.blocksBits (before++[target]) suffix
  have hi := (producer_half_safe code before.length hwalk).1
  have hlen : blocks.length+1 = before.length+2 := by simp [blocks]
  have hb : blocks.length+1 ≤ 5 := by omega
  have hdispatch := terminal_to_selector code before.length gap hwalk head leftTail (2*bank)
  have hword : pushBit (gap+1) true (2*bank) = IncrementSelector.blocksBits blocks targetTail := by
    dsimp [blocks,bank,targetTail]
    rw [IncrementMeaning.blocks_append]
    exact (IncrementMeaning.blocks_cons gap before _).symm
  have hstate : HalfPreparation.selector before.length = HalfSelector.state (blocks.length+1) := by
    rw [hlen]
    simp only [HalfPreparation.selector,HalfSelector.state]
    congr 1 <;> omega
  rw [hword,hstate] at hdispatch
  have hselect := HalfSelector.literal_select blocks hb (head+1)
    (2*bits (pathLeft code) leftTail) targetTail
  have htarget : targetTail.testBit 0 = true ∧ targetTail/2 = runPattern true target false suffix := by
    simp only [targetTail,IncrementSelector.blocksBits,IncrementSelector.odd_bit,IncrementSelector.odd_tail,
      and_self]
  rw [htarget.1,htarget.2] at hselect
  rw [silent_add,hdispatch]
  simp only [Option.bind_some]
  exact hselect

theorem terminal_to_target_physical (code : List Bool) (gap target : Nat) (before : List Nat)
    (hwalk : walk 162 code = some (.half before.length)) (head : Int) (leftTail suffix : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨halfTerminal before.length,head,bits (pathLeft code) leftTail,false,
      2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) suffix)⟩ physical) :
    let blocks := gap::before
    let steps := (2*gap+5)+pathCost code+IncrementSelector.cost blocks
    Rel ⟨HalfSelector.state 0,head+1+IncrementSelector.cost blocks,
      DecrementSelector.leftAfter blocks (2*bits (pathLeft code) leftTail),true,
      runPattern true target false suffix⟩
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  have hp := silent_physical Record285.machine _ physical hrel _ _
    (terminal_to_target code gap target before hwalk head leftTail suffix)
  refine ⟨hp.1,hp.2,?_⟩
  omega

/-- Literal dispatch from the clean root to any native-half terminal. -/
theorem root_dispatch_half (code : List Bool) (i : Nat)
    (hwalk : walk 162 code = some (.half i)) (head : Int) (leftTail rightTail : Nat) :
    silent Record285.machine code.length (rootEntry code head leftTail rightTail) =
      some ⟨halfTerminal i,head,bits (pathLeft code) leftTail,false,rightTail⟩ := by
  have hr := (producer_half_safe code i hwalk).2.1
  have hs := route_scan code treeRoot (halfTerminal i) hr
    (-(code.length:Int)) false rootLeft []
  have hz : -(code.length:Int)+(code.length:Int) = 0 := by omega
  have hh := run_sound code.length
    (rightWord treeRoot (-(code.length:Int)) code false rootLeft [])
    ⟨halfTerminal i,0,code.reverse++rootLeft,false,[]⟩
    (by simpa only [hz] using hs) head leftTail rightTail
  simpa only [rootEntry,denote,Int.add_zero,bits,pathLeft,rootLeft,List.append_assoc] using hh

/-- From a clean grammar root, the physical machine reaches the actual
selected unary field, with exact full tape and positive silent progress. The
native-half quotient and its parity-dependent continuation are not included. -/
theorem root_to_half_target_physical (code : List Bool) (gap target : Nat) (before : List Nat)
    (hwalk : walk 162 code = some (.half before.length)) (head : Int) (leftTail suffix : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (rootEntry code head leftTail
      (2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) suffix))) physical) :
    let blocks := gap::before
    let steps := code.length+(2*gap+5)+pathCost code+IncrementSelector.cost blocks
    Rel ⟨HalfSelector.state 0,head+1+IncrementSelector.cost blocks,
      DecrementSelector.leftAfter blocks (2*bits (pathLeft code) leftTail),true,
      runPattern true target false suffix⟩
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  dsimp only
  have hd := root_dispatch_half code before.length hwalk head leftTail
    (2*runPattern false gap true (2*IncrementSelector.blocksBits (before++[target]) suffix))
  have ht := terminal_to_target code gap target before hwalk head leftTail suffix
  have hs : silent Record285.machine
      (code.length+(2*gap+5)+pathCost code+IncrementSelector.cost (gap::before))
      (rootEntry code head leftTail
        (2*runPattern false gap true
          (2*IncrementSelector.blocksBits (before++[target]) suffix))) =
      some ⟨HalfSelector.state 0,head+1+IncrementSelector.cost (gap::before),
        DecrementSelector.leftAfter (gap::before) (2*bits (pathLeft code) leftTail),true,
        runPattern true target false suffix⟩ := by
    rw [show code.length+(2*gap+5)+pathCost code+IncrementSelector.cost (gap::before) =
      code.length+((2*gap+5)+pathCost code+IncrementSelector.cost (gap::before)) by omega,
      silent_add,hd]
    simpa only [Option.bind_some] using ht
  have hp := silent_physical Record285.machine _ physical hrel _ _ hs
  exact ⟨hp.1,hp.2,by omega⟩


end Shared.PNP.Record285.HalfDispatch
