import Shared.Beeping.NPcoNP.Source284GraphControllerStep
import Shared.Beeping.NPcoNP.Source284EntryController
import Shared.Beeping.ScalarWordRefinement

/-! Progress-sensitive ordered-word refinement from the shared rejection
controller to the pinned producer register graph. This is not a tape-table
refinement or a canonical complexity characterization. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphControllerRefinement
open PASoundness PASoundness.RegisterMachine Shared.Beeping
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphControllerStep
abbrev Bank := PASoundness.RegisterMachine.Bank 12
abbrev Cfg := PASoundness.RegisterMachine.Config 12 185
abbrev source := ScalarWordRefinement.beepBits (Controller.system Source284Comparison.compare 0)

def Scratch (b : Bank) : Prop := b 9=0 ∧ b 10=0 ∧ b 11=0

def Rel : Controller.State → Cfg → Prop
  | .startup, t => t.state=0 ∧ t.bank 3=0 ∧ Scratch t.bank
  | .testing e n, t => t.state=2 ∧ t.bank 3=e ∧ t.bank 4=n ∧ Scratch t.bank

/-- A mathematical segment length extracted from the proved totality theorem.
This choice is proof bookkeeping; it is not part of the executing graph. -/
noncomputable def comparisonTime (b : Bank) : Nat := by
  classical
  exact if h : Scratch b then Classical.choose (controller_step b h.1 h.2.1 h.2.2) else 1

theorem comparisonTime_spec (b : Bank) (h : Scratch b) :
    ∃ out, 0 < comparisonTime b ∧
      target.system.advance ⟨2,b⟩ (comparisonTime b) = ⟨2,out⟩ ∧
      target.system.wordFrom ⟨2,b⟩ (comparisonTime b) =
        (if Source284Comparison.compare (b 3) (b 4) then [] else [true]) ∧
      out 3 = (if Source284Comparison.compare (b 3) (b 4) then b 3 else b 3+1) ∧
      out 4 = (if Source284Comparison.compare (b 3) (b 4) then b 4+1 else 0) ∧
      Scratch out := by
  classical
  have ht : comparisonTime b = Classical.choose (controller_step b h.1 h.2.1 h.2.2) := by
    unfold comparisonTime
    rw [dif_pos h]
  rw [ht]
  obtain ⟨out,hp,ha,hw,h3,h4,h9,h10,h11⟩ :=
    Classical.choose_spec (controller_step b h.1 h.2.1 h.2.2)
  exact ⟨out,hp,ha,hw,h3,h4,h9,h10,h11⟩

noncomputable def duration : Controller.State → Cfg → Nat
  | .startup, t => t.bank 4+2
  | .testing _ _, t => comparisonTime t.bank

/-- The source controller and actual register graph have the same ordered
beeps, with positive finite segments and cofinal target coverage. -/
noncomputable def simulation : PASoundness.SegmentSimulation source target.system where
  Rel := Rel
  startup := 0
  initial := by
    simp [Rel,Scratch,source,ScalarWordRefinement.beepBits,WordEventSystem.map,
      WordEventSystem.ofBeep,Controller.system,target,MaskInvariant.Program.system,
      Parent290MaskData.program]
  startup_silent := rfl
  duration := duration
  positive := by
    intro s t h
    cases s with
    | startup => simp [duration]
    | testing e n =>
      obtain ⟨out,hp,_⟩ := comparisonTime_spec t.bank h.2.2.2
      exact hp
  next := by
    intro s t h
    cases s with
    | startup =>
      rcases t with ⟨q,b⟩
      rcases h with ⟨hq,h3,hs⟩
      change q=0 at hq
      change b 3=0 at h3
      change Scratch b at hs
      subst q
      have hr := restart b
      change Rel (.testing 0 0) (target.system.advance ⟨0,b⟩ (b 4+2))
      rw [hr.1]
      simp [Rel,Scratch,write,h3,hs.1,hs.2.1,hs.2.2]
    | testing e n =>
      rcases t with ⟨q,b⟩
      rcases h with ⟨hq,h3,h4,hs⟩
      change q=2 at hq
      change b 3=e at h3
      change b 4=n at h4
      change Scratch b at hs
      subst q
      obtain ⟨out,hp,ha,hw,ho3,ho4,hos⟩ := comparisonTime_spec b hs
      simp only [duration]
      rw [ha]
      cases hc : Source284Comparison.compare e n <;>
        simp_all [source,ScalarWordRefinement.beepBits,WordEventSystem.map,
          WordEventSystem.ofBeep,Controller.system,Controller.step,Rel,Scratch]
  word_eq := by
    intro s t h
    cases s with
    | startup =>
      rcases t with ⟨q,b⟩
      rcases h with ⟨hq,h3,hs⟩
      change q=0 at hq
      change b 3=0 at h3
      change Scratch b at hs
      subst q
      have hr := restart b
      change target.system.wordFrom ⟨0,b⟩ (b 4+2) = [true]
      exact hr.2
    | testing e n =>
      rcases t with ⟨q,b⟩
      rcases h with ⟨hq,h3,h4,hs⟩
      change q=2 at hq
      change b 3=e at h3
      change b 4=n at h4
      change Scratch b at hs
      subst q
      obtain ⟨out,hp,ha,hw,ho3,ho4,hos⟩ := comparisonTime_spec b hs
      simp only [duration]
      rw [hw,h3,h4]
      cases hc : Source284Comparison.compare e n <;>
        simp [source,ScalarWordRefinement.beepBits,WordEventSystem.map,
          WordEventSystem.ofBeep,Controller.system,Controller.step,hc]

theorem same_output : SameOutput source target.system := simulation.sameOutput

end Shared.Beeping.NPcoNP.Source284GraphControllerRefinement
