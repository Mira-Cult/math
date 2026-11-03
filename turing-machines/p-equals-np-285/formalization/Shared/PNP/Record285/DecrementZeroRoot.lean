import Shared.PNP.Record285.DecrementControl

/-! Complete clean zero decrement through break, cleanup, and root return. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.DecrementZeroRoot
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementReturn (atLeftWord)
open Shared.PNP.Record285.IncrementCleanup (peel)
open Shared.PNP.Record285.IncrementPreparation (dispatch0)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
attribute [local irreducible] Record285.machine

/-- The literal root executes any decrement grammar word to its clean
terminal without changing the unlisted tape tails or emitting an event. -/
theorem root_dispatch_decrement (code : List Bool) (i : Nat)
    (hwalk : walk 162 code = some (.dec i)) (head : Int) (leftTail rightTail : Nat) :
    silent Record285.machine code.length (rootEntry code head leftTail rightTail) =
      some ⟨decTerminal i,head,bits (pathLeft code) leftTail,false,rightTail⟩ := by
  have hr := (producer_decrement_safe code i hwalk).2.1
  have hs := route_scan code treeRoot (decTerminal i) hr
    (-(code.length:Int)) false rootLeft []
  have hz : -(code.length:Int)+(code.length:Int) = 0 := by omega
  have hh := run_sound code.length
    (rightWord treeRoot (-(code.length:Int)) code false rootLeft [])
    ⟨decTerminal i,0,code.reverse++rootLeft,false,[]⟩
    (by simpa only [hz] using hs) head leftTail rightTail
  simpa only [rootEntry,denote,Int.add_zero,bits,pathLeft,rootLeft,List.append_assoc] using hh

/-- Any frozen grammar decrement with a zero target returns to state 284.
The duration and entire resulting tape are given explicitly. -/
theorem terminal_zero_returns_root (code : List Bool) (gap : Nat) (before : List Nat)
    (hwalk : walk 162 code = some (.dec before.length)) (head : Int) (leftTail suffix : Nat) :
    let p := peel code.reverse
    let q := peel p.2
    let precode := q.2.reverse
    let bank := IncrementSelector.blocksBits (before++[0]) suffix
    let rightTail := runPattern false (p.1+q.1+gap+2) true (2*bank)
    let steps := (2*gap+5)+pathCost code+2*IncrementSelector.cost (gap::before)+4+
      (3*(p.1+q.1)+2*gap+12)+(precode.length+17)
    silent Record285.machine steps
      ⟨decTerminal before.length,head,bits (pathLeft code) leftTail,false,
        2*runPattern false gap true (2*bank)⟩ =
      some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1-q.1-2) leftTail rightTail) := by
  dsimp only
  let p := peel code.reverse
  let q := peel p.2
  let precode := q.2.reverse
  let bank := IncrementSelector.blocksBits (before++[0]) suffix
  let rightTail := runPattern false (p.1+q.1+gap+2) true (2*bank)
  have hc := decrement_control_preserves_root code before.length hwalk
  have hfirst := DecrementZeroCleanup.terminal_zero_to_dispatch code gap before hwalk head leftTail suffix
  dsimp only at hfirst
  rw [hc.2.1,hc.1] at hfirst
  change silent Record285.machine
    ((2*gap+5)+pathCost code+2*IncrementSelector.cost (gap::before)+4+
      (3*(p.1+q.1)+2*gap+12))
    ⟨decTerminal before.length,head,bits (pathLeft code) leftTail,false,
      2*runPattern false gap true (2*bank)⟩ =
    some (atLeftWord dispatch0 (head-p.1-q.1-3) (bits (q.2++rootLeft) leftTail)
      (1+2*runPattern false (p.1+q.1+gap+3) true (2*bank))) at hfirst
  have hpref : pathLeft precode = q.2++rootLeft := by
    simp [precode,pathLeft,rootLeft,List.append_assoc]
  have hword : 1+2*runPattern false (p.1+q.1+gap+3) true (2*bank) =
      1+4*rightTail := by
    dsimp only [rightTail]
    rw [show p.1+q.1+gap+3 = (p.1+q.1+gap+2)+1 by omega,runPattern]
    simp only [bitVal,Bool.false_eq_true,if_false]
    omega
  have hreturn := literal_return_root precode hc.2.2.2 (head-p.1-q.1-2) leftTail rightTail
  have hpos : (head-p.1-q.1-2)-1 = head-p.1-q.1-3 := by omega
  rw [hpref,hpos,← hword] at hreturn
  rw [silent_add,hfirst]
  simp only [Option.bind_some]
  exact hreturn

/-- The frozen grammar, source-level skip-one rule, and full physical
zero-decrement root-to-root segment, with exact event accounting. -/
theorem bound_terminal_zero_returns_root_physical (code : List Bool) (gap : Nat)
    (before : List Nat) (hwalk : walk 162 code = some (.dec before.length))
    (head : Int) (leftTail suffix : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨decTerminal before.length,head,bits (pathLeft code) leftTail,false,
      2*runPattern false gap true (2*IncrementSelector.blocksBits (before++[0]) suffix)⟩ physical) :
    let p := peel code.reverse
    let q := peel p.2
    let precode := q.2.reverse
    let bank := IncrementSelector.blocksBits (before++[0]) suffix
    let rightTail := runPattern false (p.1+q.1+gap+2) true (2*bank)
    let steps := (2*gap+5)+pathCost code+2*IncrementSelector.cost (gap::before)+4+
      (3*(p.1+q.1)+2*gap+12)+(precode.length+17)
    Grammar.literal = String.ofList (headerChars ++ renderEntries entries ++ renderedSuffix) ∧
    returnPathSkipOne code = some (precode++[true]) ∧
    Rel (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
      (head-p.1-q.1-2) leftTail rightTail)
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  have hp := silent_physical Record285.machine _ physical hrel _ _
    (terminal_zero_returns_root code gap before hwalk head leftTail suffix)
  have hc := decrement_control_preserves_root code before.length hwalk
  exact ⟨literal_typed_serialization,hc.2.2.1,hp.1,hp.2,by omega⟩

/-- Every zero-target decrement grammar path forms one finite, silent
root-to-root physical segment, including its skip-one control successor. -/
theorem bound_root_zero_returns_root_physical (code : List Bool) (gap : Nat)
    (before : List Nat) (hwalk : walk 162 code = some (.dec before.length))
    (head : Int) (leftTail suffix : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (rootEntry code head leftTail
      (2*runPattern false gap true (2*IncrementSelector.blocksBits (before++[0]) suffix))) physical) :
    let p := peel code.reverse
    let q := peel p.2
    let precode := q.2.reverse
    let bank := IncrementSelector.blocksBits (before++[0]) suffix
    let rightTail := runPattern false (p.1+q.1+gap+2) true (2*bank)
    let inner := (2*gap+5)+pathCost code+2*IncrementSelector.cost (gap::before)+4+
      (3*(p.1+q.1)+2*gap+12)+(precode.length+17)
    let steps := code.length+inner
    Grammar.literal = String.ofList (headerChars ++ renderEntries entries ++ renderedSuffix) ∧
    returnPathSkipOne code = some (precode++[true]) ∧
    Rel (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
      (head-p.1-q.1-2) leftTail rightTail)
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  dsimp only
  let tail := 2*runPattern false gap true (2*IncrementSelector.blocksBits (before++[0]) suffix)
  let p := peel code.reverse
  let q := peel p.2
  let precode := q.2.reverse
  let bank := IncrementSelector.blocksBits (before++[0]) suffix
  let inner := (2*gap+5)+pathCost code+2*IncrementSelector.cost (gap::before)+4+
    (3*(p.1+q.1)+2*gap+12)+(precode.length+17)
  have hd := root_dispatch_decrement code before.length hwalk head leftTail tail
  have ht := terminal_zero_returns_root code gap before hwalk head leftTail suffix
  have he : silent Record285.machine (code.length+inner) (rootEntry code head leftTail tail) =
      some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1-q.1-2) leftTail (runPattern false (p.1+q.1+gap+2) true (2*bank))) := by
    rw [silent_add,hd]
    simpa only [Option.bind_some] using ht
  have hp := silent_physical Record285.machine _ physical hrel _ _ he
  have hc := decrement_control_preserves_root code before.length hwalk
  exact ⟨literal_typed_serialization,hc.2.2.1,hp.1,hp.2,by omega⟩

end Shared.PNP.Record285.DecrementZeroRoot
