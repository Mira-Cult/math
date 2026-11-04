import Shared.PNP.Record285.PythonControlRelocationTransfer

/-! Express the remaining finite-segment boundary obligation on the already
proved candidate execution, rather than on the reference execution. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlRelocationCandidate
open Shared.Beeping
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlRelocation
open Shared.PNP.Record285.PythonControlRelocationStep
open Shared.PNP.Record285.PythonControlRelocationInside
open Shared.PNP.Record285.PythonControlRelocationRun
open Shared.PNP.Record285.PythonControlRelocationTransfer
open Shared.PNP.Record285.PythonControlSkip

def CandidateBefore : Status → Prop
  | .fault => True
  | .returned _ => False
  | .live c => (settle c.pc c.loops).1 < 112

theorem before_iff (r c : Status) (h : BoundedMatched r c) :
    BeforeBoundary r ↔ CandidateBefore c := by
  cases r with
  | returned n => cases c <;> simp [BoundedMatched,Matched] at h
  | fault => cases c <;> simp [BoundedMatched,Matched,BeforeBoundary,CandidateBefore] at h ⊢
  | live rc =>
    cases c with
    | fault => simp [BoundedMatched,Matched] at h
    | returned n => simp [BoundedMatched,Matched] at h
    | live cc =>
      rcases h with ⟨⟨hstore,hpc,inner,hloops,hcloops⟩,hlo,hhi,inside,hiloops,hheads⟩
      have heq : inside=inner := List.append_cancel_right (hiloops.symm.trans hloops)
      subst inside
      cases rc with
      | mk pc s loops =>
        cases cc with
        | mk pc' s' loops' =>
          simp only at *
          subst loops
          subst loops'
          subst s'
          subst pc'
          obtain ⟨target,remaining,htlo,hthi,hr,hc⟩ := settle_shared pc inner hlo hhi hheads
          simp only [BeforeBoundary,CandidateBefore,hr,hc,Prod.fst]
          omega

theorem candidate_bounded_runs (r c : Status) (h : BoundedMatched r c) (n : Nat)
    (hbefore : ∀ t, t<n → CandidateBefore ((execution c).run t)) :
    BoundedMatched ((execution r).run n) ((execution c).run n) ∧
      ∀ t, t<n → (step code ((execution r).run t)).2 =
        (step code ((execution c).run t)).2 := by
  induction n with
  | zero => exact ⟨h,by simp⟩
  | succ n ih =>
    obtain ⟨hn,hevents⟩ := ih (fun t ht => hbefore t (by omega))
    have hstep := bounded_step ((execution r).run n) ((execution c).run n) hn
      ((before_iff _ _ hn).2 (hbefore n (by omega)))
    refine ⟨hstep.2,?_⟩
    intro t ht
    by_cases htn : t<n
    · exact hevents t htn
    · have : t=n := by omega
      simpa [this] using hstep.1

theorem transfer_segment (s out : Store) (n : Nat)
    (hsegment : Silent (candidateEntry s) (candidateExit out) n)
    (hbefore : ∀ t, t<n → CandidateBefore (pySystem.advance (candidateEntry s) t)) :
    Silent (referenceEntry s) (referenceExit out) n := by
  have hbefore' : ∀ t, t<n → CandidateBefore ((execution (candidateEntry s)).run t) := by
    intro t ht
    rw [run_advance]
    exact hbefore t ht
  obtain ⟨hm,hevents⟩ := candidate_bounded_runs _ _ (initial_matched s) n hbefore'
  have hc : (execution (candidateEntry s)).run n = candidateExit out := by
    rw [run_advance]
    exact hsegment.1
  rw [hc] at hm
  constructor
  · rw [← run_advance]
    exact matched_exit _ out hm.1
  · intro t ht hbeep
    have he := hevents t ht
    have hnot := hsegment.2 t ht
    unfold EventSystem.BeepFrom at hbeep hnot
    rw [← run_advance] at hbeep hnot
    exact hnot (by simpa [pySystem] using he.symm.trans hbeep)

end Shared.PNP.Record285.PythonControlRelocationCandidate
