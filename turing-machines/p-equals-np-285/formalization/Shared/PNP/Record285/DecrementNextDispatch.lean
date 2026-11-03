import Shared.PNP.Record285.DecrementComplete
import Shared.PNP.Record285.GrammarAutoDispatch

/-! Composition of either completed decrement branch with the next literal
dispatcher segment. This does not identify or execute the next operation. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.DecrementComplete
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementCleanup (peel)
open Shared.PNP.Record285.IncrementShift (suffixBits)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar

def resultOrigin (code : List Bool) (head : Int) : Nat → Int
  | 0 => head-(peel code.reverse).1-(peel (peel code.reverse).2).1-2
  | _+1 => head-(peel code.reverse).1-1

def resultSuffix (code : List Bool) (gap : Nat) (before fields : List Nat)
    (retained : Nat) : Nat → Nat
  | 0 =>
    let p := peel code.reverse
    let q := peel p.2
    let bank := IncrementSelector.blocksBits (before++[0]) (suffixBits fields retained)
    runPattern false (p.1+q.1+gap+2) true (2*bank)
  | k+1 =>
    let p := peel code.reverse
    let bank := IncrementSelector.blocksBits (before++[k]++fields++[0]) retained
    runPattern false (p.1+gap+1) true (2*bank)

theorem result_config_layout (code : List Bool) (gap target : Nat)
    (before fields : List Nat) (head : Int) (leftTail retained : Nat) :
    resultConfig code gap before fields head leftTail retained target =
      denote (rightWord treeRoot (-(resultPrefix code target |>.length : Int))
        (resultPrefix code target) true rootLeft [false])
        (resultOrigin code head target) leftTail (resultSuffix code gap before fields retained target) := by
  cases target <;> rfl

/-- A completed decrement (including either branch) is followed by a second
positive, bounded, silent dispatcher segment selected from the actual output
tape. Both complete intermediate and final configurations are retained. -/
theorem decrement_then_dispatch (code : List Bool) (gap target : Nat)
    (before fields : List Nat) (hwalk : walk 162 code = some (.dec before.length))
    (head : Int) (leftTail retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (rootEntry code head leftTail
      (2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields retained)))) physical) :
    let word := resultPrefix code target
    let origin := resultOrigin code head target
    let suffix := resultSuffix code gap before fields retained target
    let rootHead := origin-word.length
    let w := bits (word++[true]) (bits [false] suffix)
    ∃ steps len e pre bit row, 0 < steps ∧ 0 < len ∧ len ≤ 163 ∧ isLeaf e = true ∧
      resultControl code target = some (word++[true]) ∧
      window (tapeStream w) 0 len = pre++[bit] ∧ expected e bit = some row ∧
      Rel (resultConfig code gap before fields head leftTail retained target)
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
      Rel (denote (leafDestinationAny row pre (tapeStream w len)) (rootHead+len)
        leftTail (dropTape (len+1) w))
        ((Shared.Beeping.EventSystem.mk
          ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps)
          Record285.machine.step).run len) ∧
      (∀ t, t < len → ¬ (Shared.Beeping.EventSystem.mk
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps)
        Record285.machine.step).BeepAt t) := by
  dsimp only
  obtain ⟨hc,steps,hpos,hroot,hsilent⟩ :=
    root_decrement_complete code gap target before fields hwalk head leftTail retained physical hrel
  have hroot' := hroot
  rw [result_config_layout] at hroot'
  have hhead : resultOrigin code head target - (resultPrefix code target).length +
      (resultPrefix code target).length = resultOrigin code head target := by omega
  have hd := root_word_dispatch (resultPrefix code target) true
    (resultOrigin code head target-(resultPrefix code target).length) [false] leftTail
    (resultSuffix code gap before fields retained target)
    ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) (by
      rw [hhead]
      exact hroot')
  obtain ⟨e,len,pre,bit,row,hlpos,hlbound,hleaf,hcode,hexpected,hend,hquiet⟩ := hd
  exact ⟨steps,len,e,pre,bit,row,hpos,hlpos,hlbound,hleaf,hc,hcode,hexpected,hroot,hsilent,hend,hquiet⟩

end Shared.PNP.Record285.DecrementComplete
