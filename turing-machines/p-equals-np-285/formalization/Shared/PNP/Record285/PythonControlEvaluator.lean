import Shared.PNP.Record285.PythonControlClock

/-! Complete bounded candidate evaluator in the typed source control model.
This proves no CPython parser theorem or unbounded controller correspondence. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlEvaluator
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSkip
open Shared.PNP.Record285.PythonControlActionMeaning
open Shared.PNP.Record285.PythonControlClock

theorem sameAdvance {α : Type} (a b : Shared.Beeping.EventSystem α)
    (h : a.step=b.step) (c : α) (n : Nat) : a.advance c n=b.advance c n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Shared.Beeping.EventSystem.advance,ih,h]

theorem sameBeep {α : Type} (a b : Shared.Beeping.EventSystem α)
    (h : a.step=b.step) (c : α) (n : Nat) : a.BeepFrom c n ↔ b.BeepFrom c n := by
  simp only [Shared.Beeping.EventSystem.BeepFrom,sameAdvance a b h c n,h]

/-- Every finite candidate clock finishes silently, preserves the candidate
program, and toggles `expected` exactly when the source virtual evaluator
halts within the clock. This includes zero clocks and final-step HALT. -/
theorem candidate_loop (clock : Nat) (s : Store) (hclock : s "steps"=clock) :
    ∃ duration out, 0 < duration ∧ Silent (pending s) (done out) duration ∧
      out "program" = s "program" ∧
      out "expected" =
        if haltedWithin (s "program") clock (before s) then
          (if s "expected"=0 then 1 else 0)
        else s "expected" := by
  induction clock generalizing s with
  | zero =>
    have hz : s "steps"=0 := hclock
    exact ⟨1,s,by decide,zero_tick s hz,rfl,by simp [haltedWithin]⟩
  | succ clock ih =>
    have hp : 0 < s "steps" := by omega
    let marked := prepared s
    have hsteps : marked "steps"=clock := by simp [marked,prepared,put,hclock]
    have hprogram : marked "program"=s "program" := by simp [marked,prepared,put]
    have hdigit : marked "digit"=s "program" := by simp [marked,prepared,put]
    have hexpected : marked "expected"=s "expected" := by simp [marked,prepared,put]
    have hbefore : before marked = before s := by simp [before,marked,prepared,put]
    have htick : Silent (pending s) (.live ⟨94,marked,context⟩) 3 := positive_tick s hp
    obtain ⟨d,mid,loops,hd,hact,hmidsteps,hmidprogram,hcase⟩ := candidate_action_matches marked
    rw [hdigit,hbefore] at hcase
    cases hr : simStep (s "program") (before s) with
    | none =>
      rw [hr] at hcase
      obtain ⟨hloops,htoggle⟩ := hcase
      subst loops
      have hresult : Silent (pending s) (done mid) (3+d) := silent_trans htick hact
      refine ⟨3+d,mid,by omega,hresult,?_,?_⟩
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
      obtain ⟨e,out,he,hrest,houtprog,houtexp⟩ := ih mid hmidclock
      have hresult := silent_trans (silent_trans htick hact) hrest
      refine ⟨3+d+e,out,by omega,hresult,houtprog.trans hmidprog,?_⟩
      simpa [haltedWithin,hr,hmidprog,hmidexp,hmidbefore] using houtexp

/-- The same theorem starts at the real first clock header, before any loop
frame is installed. -/
theorem candidate_from_head (s : Store) :
    ∃ duration out, 0 < duration ∧ Silent (head s) (done out) duration ∧
      out "program" = s "program" ∧
      out "expected" =
        if haltedWithin (s "program") (s "steps") (before s) then
          (if s "expected"=0 then 1 else 0)
        else s "expected" := by
  obtain ⟨n,out,hn,hquiet,hprog,hexp⟩ := candidate_loop (s "steps") s rfl
  exact ⟨n,out,hn,same_silent (head_step s) hn hquiet,hprog,hexp⟩

/-- The complete typed candidate block, beginning at source row 82, reaches
the comparison dispatch for every positive radix and exactly matches the
source candidate's bounded acceptance result. -/
theorem candidate_from_setup (s : Store) (hradix : 0 < s "radix") :
    ∃ duration out, 0 < duration ∧
      Silent (.live ⟨82,s,Shared.PNP.Record285.PythonControlCandidate.frames⟩) (done out) duration ∧
      out "program" = s "program" ∧
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
  obtain ⟨m,out,hm,hloop,hprog,hexp⟩ := candidate_from_head setup
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
  refine ⟨duration+m,out,by omega,?_,?_,?_⟩
  · exact h
  · exact hprog.trans hsetupProg
  · rw [hsetupProg,hsetupSteps,hsetupBefore,hsetupExpected] at hexp
    exact hexp

end Shared.PNP.Record285.PythonControlEvaluator
