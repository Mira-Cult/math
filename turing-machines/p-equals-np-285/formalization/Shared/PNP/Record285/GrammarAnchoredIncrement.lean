import Shared.PNP.Record285.GrammarReady

/-! Increment preserves the exact valid control, root and anchor coordinates. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarReady
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementShift (suffixBits)
open Shared.PNP.Record285.IncrementCleanup (peel)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarPrefix
open Shared.PNP.Record285.CleanBank

/-- At a zero-marked literal increment leaf, the exact complete run updates
its selected field and returns to a valid prefix at the same root and anchor. -/
theorem increment_anchored (before fields : List Nat) (target : Nat)
    (rootHead anchor head : Int) (leftTail gap : Nat) (code : List Bool)
    (physical : Shared.Beeping.Machines.Config 285)
    (hleaf : ZeroLeaf (before++[target]++fields) rootHead anchor (.inc before.length)
      code head leftTail gap physical) :
    ∃ steps, 0 < steps ∧
      AnchoredRoot (before++[target+1]++fields) rootHead anchor
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  obtain ⟨hwalk,hhead,hanchor,hroot⟩ := hleaf
  rw [split_bank] at hroot
  obtain ⟨steps,hpos,hpath,hresult,hquiet⟩ := PreparedIncrement.root_increment_both_markers
    gap target before fields code hwalk false head leftTail
    (2*runPattern false gap true
      (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields 0)))
    0 rfl physical hroot
  let p := peel code.reverse
  let word := p.2.reverse
  have hvalid : valid (word++[true]) := return_path_valid code _ _ hwalk hpath
  have hlen := (increment_return_path code before.length hwalk).2.2
  have hehead : head-p.1-1-word.length = rootHead := by
    dsimp [word,p] at *
    simp only [List.length_append,List.length_singleton] at hlen
    omega
  have heanchor : head-p.1-1+2+(p.1+gap+1 : Nat) = anchor := by omega
  refine ⟨steps,hpos,⟨word,true,head-p.1-1,leftTail,p.1+gap+1,hvalid,hehead,heanchor,?_⟩,hquiet⟩
  simpa only [IncrementMeaning.blocks_append] using hresult

end Shared.PNP.Record285.GrammarReady
