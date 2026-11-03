import Shared.PNP.Record285.SymbolicDispatch

/-! Complete ordinary increment from a clean terminal through redispatch to
its physical break state, with exact full tape and event accounting. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.IncrementTerminal
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementReturn (atLeftWord)
open Shared.PNP.Record285.IncrementPreparation
open Shared.PNP.Record285.SymbolicDispatch

/-- Exact silent execution from a clean terminal to break state. The control
word is arbitrary but must pass the explicit verified path checker, and has six
zero cells to its left. All remaining tape data is arbitrary. -/
theorem literal_terminal_increment_code (gap target : Nat) (before suffix : List Nat)
    (hindex : before.length < 15) (code : List Bool)
    (hcode : pathCheck code before.length = true) (head : Int) (leftTail retained : Nat) :
    let i := before.length
    let left := bits (pathLeft code) leftTail
    let bank := IncrementSelector.blocksBits (before++[target])
      (IncrementShift.suffixBits suffix retained)
    let selected := gap::(before++[target])
    let steps := (2*gap+5) + pathCost code +
      2*(IncrementSelector.cost selected+IncrementShift.cost suffix)
    silent Record285.machine steps
      ⟨terminal i,head,left,false,2*runPattern false gap true (2*bank)⟩ =
      some (atLeftWord IncrementReturn.breakState (head-1) left
        (4*IncrementSelector.blocksBits (gap::(before++[target+1]))
          (IncrementSelector.blocksBits suffix retained))) := by
  dsimp only
  let i := before.length
  let left := bits (pathLeft code) leftTail
  let bank := IncrementSelector.blocksBits (before++[target])
    (IncrementShift.suffixBits suffix retained)
  let selected := gap::(before++[target])
  have hlen : selected.length = i+2 := by dsimp [selected,i]; simp
  have hb : selected.length ≤ 16 := by dsimp [i] at hlen; omega
  have hp := literal_prepare i hindex gap head left (2*bank)
  have hd := literal_redispatch_code code i hcode head leftTail (pushBit (gap+1) true (2*bank))
  have hk : pushBit (gap+1) true (2*bank) =
      IncrementSelector.blocksBits selected (IncrementShift.suffixBits suffix retained) := by
    dsimp [selected,bank]
    exact (IncrementMeaning.blocks_cons gap (before++[target])
      (IncrementShift.suffixBits suffix retained)).symm
  rw [hk, ← hlen] at hd
  have hu := IncrementMeaning.literal_increment gap target before suffix hb (head+1) retained left
  rw [show (2*gap+5)+pathCost code+
      2*(IncrementSelector.cost selected+IncrementShift.cost suffix) =
      (2*gap+5)+(pathCost code+
        2*(IncrementSelector.cost selected+IncrementShift.cost suffix)) by omega,
    silent_add,hp]
  simp only [Option.bind_some]
  rw [hk,silent_add,hd]
  simp only [Option.bind_some]
  have hh : head+1-2 = head-1 := by omega
  simpa only [hh] using hu

/-- Full physical-tape and no-spurious-event form of the clean-terminal
increment. This does not yet include lexical cleanup or source mapping. -/
theorem literal_terminal_increment_code_physical (gap target : Nat) (before suffix : List Nat)
    (hindex : before.length < 15) (code : List Bool)
    (hcode : pathCheck code before.length = true) (head : Int) (leftTail retained : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨terminal before.length,head,bits (pathLeft code) leftTail,false,
      2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (IncrementShift.suffixBits suffix retained))⟩ physical) :
    let left := bits (pathLeft code) leftTail
    let selected := gap::(before++[target])
    let steps := (2*gap+5) + pathCost code +
      2*(IncrementSelector.cost selected+IncrementShift.cost suffix)
    Rel (atLeftWord IncrementReturn.breakState (head-1) left
      (4*IncrementSelector.blocksBits (gap::(before++[target+1]))
        (IncrementSelector.blocksBits suffix retained)))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t :=
  silent_physical Record285.machine _ physical hrel _ _
    (literal_terminal_increment_code gap target before suffix hindex code hcode head leftTail retained)


/-- The complete clean-terminal segment always makes positive progress. -/
theorem terminal_steps_positive (gap target : Nat) (before suffix : List Nat) (code : List Bool) :
    0 < (2*gap+5) + pathCost code +
      2*(IncrementSelector.cost (gap::(before++[target]))+IncrementShift.cost suffix) := by
  omega

/-- One kernel-checked control path for each of the fifteen increment indices.
Other paths can use `literal_terminal_increment_code` after their own check. -/
theorem literal_terminal_increment (gap target : Nat) (before suffix : List Nat)
    (hindex : before.length < 15) (head : Int) (leftTail retained : Nat) :
    let i := before.length
    let left := bits (controlLeft i) leftTail
    let bank := IncrementSelector.blocksBits (before++[target])
      (IncrementShift.suffixBits suffix retained)
    let selected := gap::(before++[target])
    let steps := (2*gap+5) + dispatchCost i +
      2*(IncrementSelector.cost selected+IncrementShift.cost suffix)
    silent Record285.machine steps
      ⟨terminal i,head,left,false,2*runPattern false gap true (2*bank)⟩ =
      some (atLeftWord IncrementReturn.breakState (head-1) left
        (4*IncrementSelector.blocksBits (gap::(before++[target+1]))
          (IncrementSelector.blocksBits suffix retained))) := by
  have h := literal_terminal_increment_code gap target before suffix hindex (control before.length)
    (frozen_path_check before.length hindex) head leftTail retained
  simpa only [pathLeft,controlLeft,pathCost,dispatchCost] using h

theorem literal_terminal_increment_physical (gap target : Nat) (before suffix : List Nat)
    (hindex : before.length < 15) (head : Int) (leftTail retained : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨terminal before.length,head,bits (controlLeft before.length) leftTail,false,
      2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (IncrementShift.suffixBits suffix retained))⟩ physical) :
    let i := before.length
    let left := bits (controlLeft i) leftTail
    let selected := gap::(before++[target])
    let steps := (2*gap+5) + dispatchCost i +
      2*(IncrementSelector.cost selected+IncrementShift.cost suffix)
    Rel (atLeftWord IncrementReturn.breakState (head-1) left
      (4*IncrementSelector.blocksBits (gap::(before++[target+1]))
        (IncrementSelector.blocksBits suffix retained)))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t :=
  silent_physical Record285.machine _ physical hrel _ _
    (literal_terminal_increment gap target before suffix hindex head leftTail retained)

end Shared.PNP.Record285.IncrementTerminal
