import Shared.PNP.Record285.PythonControlEvaluator

/-! Complete-store frame for the candidate evaluator: arbitrary keys outside
the evaluator's scratch and result fields are retained. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlCandidateFrame
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSkip
open Shared.PNP.Record285.PythonControlAction
open Shared.PNP.Record285.PythonControlActionMeaning
open Shared.PNP.Record285.PythonControlClock
open Shared.PNP.Record285.PythonControlEvaluator

def Protected (k : String) : Prop :=
  k ≠ "left" ∧ k ≠ "right" ∧ k ≠ "state" ∧ k ≠ "write" ∧ k ≠ "direction" ∧
  k ≠ "digit" ∧ k ≠ "steps" ∧ k ≠ "expected"

def Frame (s out : Store) : Prop := ∀ k, Protected k → out k=s k

theorem frame_refl (s : Store) : Frame s s := by intro k hk; rfl

theorem frame_trans {a b c : Store} (h₁ : Frame a b) (h₂ : Frame b c) : Frame a c := by
  intro k hk
  exact (h₂ k hk).trans (h₁ k hk)

theorem action_frames (s : Store) :
    Frame s (continued (PythonControlAction.prepared (decoded s))) ∧
      Frame s (halted (PythonControlAction.prepared (decoded s))) := by
  constructor <;> intro k hk <;>
    rcases hk with ⟨hl,hr,hs,hw,hd,hdi,hst,he⟩ <;>
    simp [continued,halted,PythonControlAction.prepared,decoded,Shared.PNP.Record285.PythonControlDecode.storeOf,
      put,hl,hr,hs,hw,hd,hdi,hst,he]

theorem clock_frame (s : Store) : Frame s (PythonControlClock.prepared s) := by
  intro k hk
  rcases hk with ⟨hl,hr,hs,hw,hd,hdi,hst,he⟩
  simp [PythonControlClock.prepared,put,hdi,hst]

theorem setup_frame (s : Store) : Frame s (Shared.PNP.Record285.PythonCandidateSetup.output s) := by
  intro k hk
  rcases hk with ⟨hl,hr,hs,hw,hd,hdi,hst,he⟩
  simp [Shared.PNP.Record285.PythonCandidateSetup.output,put,hl,hr,hs,hst]

theorem candidate_action_frame_matches (s : Store) :
    ∃ n out loops, 0 < n ∧ Silent (.live ⟨94,s,context⟩) (.live ⟨131,out,loops⟩) n ∧
      out "steps" = s "steps" ∧ out "program" = s "program" ∧ Frame s out ∧
      match simStep (s "digit") (before s) with
      | none => loops = Shared.PNP.Record285.PythonControlCandidate.frames ∧
          out "expected" = (if s "expected"=0 then 1 else 0)
      | some next => loops = context ∧ after out = next ∧ out "expected" = s "expected" := by
  let d := decoded s
  let p := PythonControlAction.prepared d
  have hframe := action_frames s
  obtain ⟨n,hn,hsegment⟩ := candidate_action_terminates s
  change Silent (.live ⟨94,s,context⟩)
    (if d "state"=0 then
      .live ⟨131,halted p,Shared.PNP.Record285.PythonControlCandidate.frames⟩
     else .live ⟨131,continued p,context⟩) n at hsegment
  by_cases hz : d "state"=0
  · have hnone : simStep (s "digit") (before s) = none := (halts_iff s).2 hz
    simp only [hz,if_true] at hsegment
    refine ⟨n,halted p,Shared.PNP.Record285.PythonControlCandidate.frames,hn,hsegment,
      (action_control_fields s).2.2.1,(action_control_fields s).2.2.2,hframe.2,?_⟩
    simp only [hnone]
    exact ⟨trivial,halt_matches s⟩
  · cases hr : simStep (s "digit") (before s) with
    | none => exact False.elim (hz ((halts_iff s).1 hr))
    | some next =>
      simp only [hz,if_false] at hsegment
      obtain ⟨hnext,hexpected⟩ := continue_matches s next hr
      refine ⟨n,continued p,context,hn,hsegment,
        (action_control_fields s).1,(action_control_fields s).2.1,hframe.1,?_⟩
      simp only [hr]
      exact ⟨trivial,hnext,hexpected⟩


theorem candidate_loop_frame (clock : Nat) (s : Store) (hclock : s "steps"=clock) :
    ∃ duration out, 0 < duration ∧ Silent (pending s) (done out) duration ∧
      out "program" = s "program" ∧ Frame s out ∧
      out "expected" =
        if haltedWithin (s "program") clock (before s) then
          (if s "expected"=0 then 1 else 0)
        else s "expected" := by
  induction clock generalizing s with
  | zero =>
    have hz : s "steps"=0 := hclock
    exact ⟨1,s,by decide,zero_tick s hz,rfl,frame_refl s,by simp [haltedWithin]⟩
  | succ clock ih =>
    have hp : 0 < s "steps" := by omega
    let marked := PythonControlClock.prepared s
    have hsteps : marked "steps"=clock := by simp [marked,PythonControlClock.prepared,put,hclock]
    have hprogram : marked "program"=s "program" := by simp [marked,PythonControlClock.prepared,put]
    have hdigit : marked "digit"=s "program" := by simp [marked,PythonControlClock.prepared,put]
    have hexpected : marked "expected"=s "expected" := by simp [marked,PythonControlClock.prepared,put]
    have hbefore : before marked = before s := by simp [before,marked,PythonControlClock.prepared,put]
    have hmarked : Frame s marked := clock_frame s
    have htick : Silent (pending s) (.live ⟨94,marked,context⟩) 3 := positive_tick s hp
    obtain ⟨d,mid,loops,hd,hact,hmidsteps,hmidprogram,hmidframe,hcase⟩ := candidate_action_frame_matches marked
    rw [hdigit,hbefore] at hcase
    cases hr : simStep (s "program") (before s) with
    | none =>
      rw [hr] at hcase
      obtain ⟨hloops,htoggle⟩ := hcase
      subst loops
      have hresult : Silent (pending s) (done mid) (3+d) := silent_trans htick hact
      refine ⟨3+d,mid,by omega,hresult,?_,frame_trans hmarked hmidframe,?_⟩
      · exact hmidprogram.trans hprogram
      · simpa [haltedWithin,hr,hexpected] using htoggle
    | some next =>
      rw [hr] at hcase
      obtain ⟨hloops,hnext,hexp⟩ := hcase
      subst loops
      have hmidclock : mid "steps"=clock := hmidsteps.trans hsteps
      have hmidprog : mid "program"=s "program" := hmidprogram.trans hprogram
      have hmidexp : mid "expected"=s "expected" := hexp.trans hexpected
      have hmidbefore : before mid=next := by simpa [before,after] using hnext
      obtain ⟨e,out,he,hrest,houtprog,houtframe,houtexp⟩ := ih mid hmidclock
      have hresult := silent_trans (silent_trans htick hact) hrest
      refine ⟨3+d+e,out,by omega,hresult,houtprog.trans hmidprog,
        frame_trans (frame_trans hmarked hmidframe) houtframe,?_⟩
      simpa [haltedWithin,hr,hmidprog,hmidexp,hmidbefore] using houtexp


theorem candidate_from_head_frame (s : Store) :
    ∃ duration out, 0 < duration ∧ Silent (head s) (done out) duration ∧
      out "program" = s "program" ∧ Frame s out ∧
      out "expected" =
        if haltedWithin (s "program") (s "steps") (before s) then
          (if s "expected"=0 then 1 else 0)
        else s "expected" := by
  obtain ⟨n,out,hn,hquiet,hprog,hframe,hexp⟩ := candidate_loop_frame (s "steps") s rfl
  exact ⟨n,out,hn,same_silent (head_step s) hn hquiet,hprog,hframe,hexp⟩

/-- The complete typed candidate block, beginning at source row 82, reaches
the comparison dispatch for every positive radix and exactly matches the
source candidate's bounded acceptance result. -/
theorem candidate_from_setup_frame (s : Store) (hradix : 0 < s "radix") :
    ∃ duration out, 0 < duration ∧
      Silent (.live ⟨82,s,Shared.PNP.Record285.PythonControlCandidate.frames⟩) (done out) duration ∧
      out "program" = s "program" ∧ Frame s out ∧
      out "expected" =
        if candidate (s "program") (s "exponent") (s "n") (s "radix") (s "remaining") then
          (if s "expected"=0 then 1 else 0)
        else s "expected" := by
  let setup := Shared.PNP.Record285.PythonCandidateSetup.output s
  let duration := Shared.PNP.Record285.PythonControlCandidate.duration s
  have hpositive : 0 < duration := by
    dsimp [duration,Shared.PNP.Record285.PythonControlCandidate.duration]
    split <;> omega
  have hsetup : Silent (.live ⟨82,s,Shared.PNP.Record285.PythonControlCandidate.frames⟩)
      (head setup) duration := by
    constructor
    · rw [←sameAdvance (Shared.PNP.Record285.PythonControlCandidate.system s) pySystem rfl]
      exact Shared.PNP.Record285.PythonControlCandidate.segment s hradix
    · intro t ht
      rw [←sameBeep (Shared.PNP.Record285.PythonControlCandidate.system s) pySystem rfl]
      exact Shared.PNP.Record285.PythonControlCandidate.segment_silent s hradix t ht
  obtain ⟨m,out,hm,hloop,hprog,hframe,hexp⟩ := candidate_from_head_frame setup
  have hsetupProg : setup "program"=s "program" := by
    simp [setup,Shared.PNP.Record285.PythonCandidateSetup.output,put]
  have hsetupExpected : setup "expected"=s "expected" := by
    simp [setup,Shared.PNP.Record285.PythonCandidateSetup.output,put]
  have hsetupSteps : setup "steps"=(s "n"+2)^(s "exponent") := by
    simp [setup,Shared.PNP.Record285.PythonCandidateSetup.output,put]
  have hsetupBefore : before setup =
      ⟨0,(frame (s "radix") (s "remaining"))/2,2*((frame (s "radix") (s "remaining"))%2),0⟩ := by
    simp [before,setup,Shared.PNP.Record285.PythonCandidateSetup.output,put]
  have h := silent_trans hsetup hloop
  refine ⟨duration+m,out,by omega,?_,?_,frame_trans (setup_frame s) hframe,?_⟩
  · exact h
  · exact hprog.trans hsetupProg
  · rw [hsetupProg,hsetupSteps,hsetupBefore,hsetupExpected] at hexp
    exact hexp


end Shared.PNP.Record285.PythonControlCandidateFrame
