import Shared.PNP.Record285.HalfComplete
import Shared.PNP.Record285.GrammarAutoDispatch

/-! Compose every completed half branch with its next literal dispatch. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.HalfComplete
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementShift (suffixBits)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar

/-- Exact full-tape destination and absence of events for a positive bounded
dispatch segment. The later primitive and its source meaning are separate. -/
def NextDispatch (physical : Shared.Beeping.Machines.Config 285) : Prop :=
  ∃ len e pre bit row marker origin leftTail suffix,
    0 < len ∧ len ≤ 163 ∧ isLeaf e = true ∧ expected e bit = some row ∧
    Rel (denote (leafDestinationAny row pre marker) origin leftTail suffix)
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run len) ∧
    ∀ t, t < len → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t

theorem returned_root_dispatch (word : List Bool) (origin : Int) (leftTail suffix : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(word.length:Int)) word true rootLeft [false])
      origin leftTail suffix) physical) : NextDispatch physical := by
  let head := origin-word.length
  have hh : head+word.length = origin := by dsimp [head]; omega
  have hd := root_word_dispatch word true head [false] leftTail suffix physical (by
    rw [hh]
    exact hrel)
  obtain ⟨e,len,pre,bit,row,hpos,hbound,hleaf,_,hexpected,hresult,hquiet⟩ := hd
  exact ⟨len,e,pre,bit,row,_,_,_,_,hpos,hbound,hleaf,hexpected,hresult,hquiet⟩

theorem result_dispatch (code : List Bool) (gap target : Nat) (before fields : List Nat)
    (head : Int) (leftTail retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (h : Result code gap target before fields head leftTail retained physical) : NextDispatch physical := by
  rcases h with h | h | h | h
  · rcases h with ⟨_,_,hr⟩
    dsimp only [evenConfig] at hr
    exact returned_root_dispatch _ _ _ _ physical hr
  · rcases h with ⟨_,_,hr⟩
    dsimp only [oddConfig] at hr
    exact returned_root_dispatch _ _ _ _ physical hr
  · rcases h with ⟨_,_,_,hr⟩
    dsimp only [evenConfig] at hr
    exact returned_root_dispatch _ _ _ _ physical hr
  · rcases h with ⟨_,_,_,hr⟩
    dsimp only [oddConfig] at hr
    exact returned_root_dispatch _ _ _ _ physical hr

/-- A complete native-half action is followed by a second positive, silent
literal dispatcher segment, for every operand under the stated reserve. -/
theorem half_then_dispatch (code : List Bool) (gap target : Nat) (before fields : List Nat)
    (hwalk : walk 162 code = some (.half before.length)) (head : Int) (leftTail retained : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (rootEntry code head leftTail
      (2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target])
          (suffixBits fields (2^(target/2)*retained))))) physical) :
    ∃ steps, 0 < steps ∧
      Result code gap target before fields head leftTail retained
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      NextDispatch ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  obtain ⟨steps,hpos,hresult,hquiet⟩ :=
    root_half_complete code gap target before fields hwalk head leftTail retained physical hrel
  exact ⟨steps,hpos,hresult,result_dispatch code gap target before fields head leftTail retained _ hresult,hquiet⟩

end Shared.PNP.Record285.HalfComplete
