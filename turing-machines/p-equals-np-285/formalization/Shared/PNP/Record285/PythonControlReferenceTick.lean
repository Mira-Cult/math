import Shared.PNP.Record285.PythonControlReferenceClockMeaning

/-! One complete reference clock tick, including choice consumption and a
full virtual action, agrees with the source transition. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlReferenceTick
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSkip (Silent silent_trans)
open Shared.PNP.Record285.PythonControlActionMeaning (before after)
open Shared.PNP.Record285.PythonControlReferenceAction (outerReference)
open Shared.PNP.Record285.PythonControlReferenceActionMeaning
open Shared.PNP.Record285.PythonControlReferenceClock
open Shared.PNP.Record285.PythonControlReferenceClockMeaning
open Shared.PNP.Record285.PythonControlRelocation (referenceBase)

theorem sourceState_after (s : Store) (next : SimState) (h : after s=next) :
    sourceState s = {next with choices := s "choices"} := by
  cases next with
  | mk l r selector choices =>
    simp only [after,SimState.mk.injEq] at h
    rcases h with ⟨hl,hr,hs,hc⟩
    simp [sourceState,hl,hr,hs]

theorem positive_tick_matches (s : Store) (hp : 0 < s "steps") :
    ∃ n out loops, 0<n ∧ Silent (pending s) (.live ⟨82,out,loops⟩) n ∧
      out "steps" = s "steps"-1 ∧ out "program" = s "program" ∧
      out "radix" = s "radix" ∧ out "remaining" = s "remaining" ∧
      out "n" = s "n" ∧ out "exponent" = s "exponent" ∧
      match simStep (s "radix"+s "remaining") (sourceState s) with
      | none => loops=outerReference ∧ out "expected"=1 ∧ out "branches"=0
      | some next => loops=referenceBase ∧ sourceState out=next ∧
          out "expected"=s "expected" ∧ out "branches"=s "branches" := by
  let p := prepared s
  have hclock := positive_tick s hp
  obtain ⟨m,out,loops,hm,hseg,hsteps,hprogram,hchoices,hradix,hremaining,hname,hexponent,hresult⟩ :=
    reference_action_matches p
  have hf := prepared_fields s
  have hnames := prepared_names s
  have hchoice := choice_step s
  cases hlocal : simStep (p "digit") (before p) with
  | none =>
    have hglobal : simStep (s "radix"+s "remaining") (sourceState s)=none := by
      simpa [p,hlocal] using hchoice
    simp only [hlocal] at hresult
    refine ⟨duration s+m,out,loops,by omega,silent_trans hclock hseg,
      hsteps.trans hf.1,hprogram.trans hf.2.2.2.1,hradix.trans hf.2.2.2.2.1,
      hremaining.trans hf.2.2.2.2.2.1,hname.trans hnames.1,hexponent.trans hnames.2,?_⟩
    simpa [hglobal] using hresult
  | some next =>
    have hglobal : simStep (s "radix"+s "remaining") (sourceState s) =
        some {next with choices := s "choices"/2} := by
      simpa [p,hlocal] using hchoice
    simp only [hlocal] at hresult
    obtain ⟨hloops,hnext,hexpected,hbranches⟩ := hresult
    have hs : sourceState out = {next with choices := s "choices"/2} := by
      have hpc : p "choices" = s "choices"/2 := hf.2.2.1
      rw [sourceState_after out next hnext,hchoices,hpc]
    refine ⟨duration s+m,out,loops,by omega,silent_trans hclock hseg,
      hsteps.trans hf.1,hprogram.trans hf.2.2.2.1,hradix.trans hf.2.2.2.2.1,
      hremaining.trans hf.2.2.2.2.2.1,hname.trans hnames.1,hexponent.trans hnames.2,?_⟩
    simp only [hglobal]
    exact ⟨hloops,hs,hexpected.trans hf.2.2.2.2.2.2.1,
      hbranches.trans hf.2.2.2.2.2.2.2⟩

end Shared.PNP.Record285.PythonControlReferenceTick
