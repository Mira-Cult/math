import Shared.Beeping.NPcoNP.Grammar284ActiveWindow

/-! Arbitrary finite graph prefixes, including root and beep, match the literal
machine from a supplied active window. No reachable initialization is asserted. -/
namespace Shared.Beeping.NPcoNP.Grammar284ActiveRun
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.Grammar284ActiveWindow
open Shared.Beeping.NPcoNP.Parent290Coalesced
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

/-- Every finite graph prefix has a matching physical prefix, whose duration is
at least the number of graph steps, preserving the supplied active relation. -/
theorem prefix_runs (count : Nat) (c : PASoundness.RegisterMachine.Config 12 185)
    (origin separator : Int) (t : Int → Bool)
    (window : ActiveWindow c.state c.bank origin separator t) :
    ∃ steps out, count≤steps ∧
      ActiveWindow (target.system.advance c count).state (target.system.advance c count).bank origin separator out ∧
      physical.advance (cfg 93 (origin+1) t) steps=cfg 93 (origin+1) out ∧
      physical.wordFrom (cfg 93 (origin+1) t) steps=target.system.wordFrom c count := by
  induction count generalizing c t with
  | zero =>
    refine ⟨0,t,by omega,?_,rfl,rfl⟩
    simpa [WordEventSystem.advance] using window
  | succ count ih =>
    obtain ⟨a,mid,ha,hmid,hadv,hword⟩ := Grammar284ActiveWindow.step c.state c.bank origin separator t window
    have hcfg : (⟨c.state,c.bank⟩ : PASoundness.RegisterMachine.Config 12 185)=c := by cases c; rfl
    rw [hcfg] at hmid hword
    let next := (target.system.step c).1
    have hnext : ActiveWindow next.state next.bank origin separator mid := hmid
    obtain ⟨b,out,hb,hout,hrest,hrestword⟩ := ih next mid hnext
    have hgraphAdvance : target.system.advance c (count+1)=target.system.advance next count := by
      rw [show count+1=1+count by omega,WordEventSystem.advance_add]
      rfl
    have hgraphWord : target.system.wordFrom c (count+1)=(target.system.step c).2 ++ target.system.wordFrom next count := by
      rw [show count+1=1+count by omega,WordEventSystem.wordFrom_add]
      simp [WordEventSystem.wordFrom,WordEventSystem.advance,next]
    refine ⟨a+b,out,by omega,?_,?_,?_⟩
    · simpa only [hgraphAdvance] using hout
    · rw [WordEventSystem.advance_add,hadv,hrest]
    · rw [WordEventSystem.wordFrom_add,hadv,hword,hrestword,hgraphWord]

#print axioms prefix_runs
end Shared.Beeping.NPcoNP.Grammar284ActiveRun
