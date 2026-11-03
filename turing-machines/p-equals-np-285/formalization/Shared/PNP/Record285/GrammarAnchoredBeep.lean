import Shared.PNP.Record285.GrammarAnchoredHalf

/-! The marked action preserves the anchored valid grammar invariant. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarReady
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarPrefix
open Shared.PNP.Record285.CleanBank

theorem beep_anchored (fields : List Nat) (rootHead anchor head : Int)
    (leftTail gap : Nat) (code : List Bool) (physical : Shared.Beeping.Machines.Config 285)
    (hleaf : ZeroLeaf fields rootHead anchor .beep code head leftTail gap physical) :
    let steps := beepDuration false gap
    let sys := Shared.Beeping.EventSystem.mk physical Record285.machine.step
    0 < steps ∧ AnchoredRoot fields rootHead anchor (sys.run steps) ∧
      (∀ t, t < steps → (sys.BeepAt t ↔ t = beepEventTime false gap)) := by
  obtain ⟨hwalk,hhead,hanchor,hroot⟩ := hleaf
  have h := beep_both_markers_physical code hwalk false gap head leftTail
    (2*runPattern false gap true (2*IncrementSelector.blocksBits fields 0))
    (IncrementSelector.blocksBits fields 0) rfl physical hroot
  dsimp only at h ⊢
  have hv : valid (beepPrecode++[true]) := return_path_valid code _ _ hwalk h.2.1
  have hcode : code = beepCode := root_beep_word code hwalk
  have hlen : code.length = 3 := by rw [hcode]; rfl
  have hehead : head-1-beepPrecode.length = rootHead := by simp [beepPrecode] at *; omega
  have heanchor : head-1+2+(gap+1 : Nat) = anchor := by omega
  refine ⟨h.2.2.2.2,⟨beepPrecode,true,head-1,leftTail,gap+1,hv,hehead,heanchor,?_⟩,h.2.2.2.1⟩
  simpa [beepPrecode] using h.2.2.1

end Shared.PNP.Record285.GrammarReady
