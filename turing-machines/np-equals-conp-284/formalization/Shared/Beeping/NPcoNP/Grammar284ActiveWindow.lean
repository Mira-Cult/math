import Shared.Beeping.NPcoNP.Grammar284RootBeep
import Shared.Beeping.NPcoNP.Grammar284ReservedNonspecial

/-! A supplied active window simulates every graph instruction, including root
and beep, with matching words and positive physical progress. -/
namespace Shared.Beeping.NPcoNP.Grammar284ActiveWindow
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284ReservedWindow
open Shared.Beeping.NPcoNP.Grammar284RootReady
open Shared.Beeping.NPcoNP.Grammar284RootStep
open Shared.Beeping.NPcoNP.Grammar284RootBeep
open Shared.Beeping.NPcoNP.Grammar284BeepPrepared
open Shared.Beeping.NPcoNP.Grammar284BeepWindow
open Shared.Beeping.NPcoNP.Parent290Coalesced
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

def ActiveWindow (state : Fin 185) (bank : Bank 12) (origin separator : Int)
    (t : Int → Bool) : Prop :=
  ReservedWindow state bank origin separator t ∨ (state=0 ∧ RootReady bank origin separator t)

theorem step (state : Fin 185) (graph : Bank 12) (origin separator : Int) (t : Int → Bool)
    (window : ActiveWindow state graph origin separator t) :
    let result := target.system.step ⟨state,graph⟩
    ∃ steps out, 0<steps ∧ ActiveWindow result.1.state result.1.bank origin separator out ∧
      physical.advance (cfg 93 (origin+1) t) steps=cfg 93 (origin+1) out ∧
      physical.wordFrom (cfg 93 (origin+1) t) steps=result.2 := by
  dsimp only
  rcases window with hwindow | ⟨hstate,hready⟩
  · by_cases hzero : state=0
    · subst state
      obtain ⟨n,out,hn,hnext,ha,hw⟩ := beep_step graph origin separator t hwindow
      refine ⟨n,out,hn,?_,ha,?_⟩
      · rw [graph_beep]
        exact Or.inl hnext
      · simpa only [graph_beep] using hw
    · by_cases hroot : state=184
      · subst state
        obtain ⟨n,out,hn,hevent,hstate,hnext,hseg⟩ := root_step graph origin separator t hwindow
        obtain ⟨ha,hw⟩ := silent_physical _ _ _ hseg
        exact ⟨n,out,hn,Or.inr ⟨hstate,hnext⟩,ha,hw.trans hevent.symm⟩
      · obtain ⟨n,out,hn,hevent,hnext,hseg⟩ := Grammar284ReservedNonspecial.step state graph origin separator t hwindow hzero hroot
        obtain ⟨ha,hw⟩ := silent_physical _ _ _ hseg
        exact ⟨n,out,hn,Or.inl hnext,ha,hw.trans hevent.symm⟩
  · subst state
    obtain ⟨n,out,hn,hnext,ha,hw⟩ := root_beep_step graph origin separator t hready
    refine ⟨n,out,hn,?_,ha,?_⟩
    · rw [graph_beep]
      exact Or.inl hnext
    · simpa only [graph_beep] using hw

#print axioms step
end Shared.Beeping.NPcoNP.Grammar284ActiveWindow
