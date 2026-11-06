import Shared.Beeping.ControllerTM2Loop
import Shared.Beeping.ComparisonCommit

/-! A progress-sensitive simulation of the rejection controller by the
actual looping TM2 program. Finite comparison runs and the two explicit
output/commit blocks supply the segment lengths. -/
namespace Shared.Beeping.ControllerTM2Refinement
open Turing Turing.PartrecToTM2 Turing.ToPartrec
open Shared.Beeping.ControllerTM2Loop Shared.Beeping.ControllerCode
open Shared.Beeping.ComparisonTM2 Shared.ComplexityBridge.TM2Symbols

variable (R : Controller.Comparison) (c : Code)

def CodeCorrect : Prop := ∀ e n, c.eval [e,n] =
  pure [result R e n,candidate R e n,test R e n]

theorem evaluation_finishes (hc : CodeCorrect R c) (e n : Nat) :
    ∃ d, runSteps (TM2.step tr) d (init c [e,n]) =
      some (halt [result R e n,candidate R e n,test R e n]) := by
  have hmem : halt [result R e n,candidate R e n,test R e n] ∈
      StateTransition.eval (TM2.step tr) (init c [e,n]) := by
    rw [tr_eval,hc e n]
    change halt [result R e n,candidate R e n,test R e n] ∈
      Part.some (halt [result R e n,candidate R e n,test R e n])
    exact Part.mem_some_iff.mpr rfl
  exact reaches_runSteps (StateTransition.mem_eval.mp hmem).1

noncomputable def evalTime (hc : CodeCorrect R c) (e n : Nat) : Nat :=
  Classical.choose (evaluation_finishes R c hc e n)

theorem evalTime_correct (hc : CodeCorrect R c) (e n : Nat) :
    runSteps (TM2.step tr) (evalTime R c hc e n) (init c [e,n]) =
      some (halt [result R e n,candidate R e n,test R e n]) :=
  Classical.choose_spec (evaluation_finishes R c hc e n)

theorem advance_embed (x y : Cfg') (d : Nat)
    (h : runSteps (TM2.step tr) d x = some y) :
    (system c).advance (embed x) d = embed y := by
  induction d generalizing y with
  | zero =>
    change some x = some y at h
    cases Option.some.inj h
    rfl
  | succ d ih =>
    change (runSteps (TM2.step tr) d x).bind (TM2.step tr) = some y at h
    cases hr : runSteps (TM2.step tr) d x with
    | none => simp [hr] at h
    | some mid =>
      have hm : TM2.step tr mid = some y := by simpa [hr] using h
      change ((system c).step ((system c).advance (embed x) d)).1 = _
      rw [ih mid hr]
      simp [system,live_step c mid y hm]

theorem advance_silent (x y : Cfg') (d : Nat)
    (h : runSteps (TM2.step tr) d x = some y) (j : Nat) (hj : j ≤ d) :
    ¬ (system c).BeepFrom (embed x) j := by
  obtain ⟨mid,hm⟩ := ComparisonCommit.run_prefix (TM2.step tr) x y d j h hj
  unfold EventSystem.BeepFrom
  rw [advance_embed c x mid j hm]
  cases hm : mid.l <;> simp [system,embed,flag,hm]

def prepared (e n : Nat) : Conf := embed (init c [e,n])

def final (e n : Nat) : Conf :=
  embed (halt [result R e n,candidate R e n,test R e n])

def committing (e n : Nat) : Conf :=
  ⟨some (if R e n then .accept else .reject),none,
    K'.elim (trList [candidate R e n,test R e n]) [] [] []⟩

theorem ready_after_comparison (hc : CodeCorrect R c) (e n : Nat) :
    (system c).advance (prepared c e n) (evalTime R c hc e n) = final R e n :=
  advance_embed c _ _ _ (evalTime_correct R c hc e n)

theorem ready_after_done (hc : CodeCorrect R c) (e n : Nat) :
    (system c).advance (prepared c e n) (evalTime R c hc e n + 1) = committing R e n := by
  rw [EventSystem.advance,ready_after_comparison R c hc]
  change (TM2.step (program c) (final R e n)).getD (final R e n) = _
  simp [final,committing,result,done_step]

theorem ready_after_commit (hc : CodeCorrect R c) (e n : Nat) :
    (system c).advance (prepared c e n) (evalTime R c hc e n + 2) =
      prepared c (candidate R e n) (test R e n) := by
  rw [show evalTime R c hc e n + 2 = (evalTime R c hc e n + 1) + 1 by omega,
    EventSystem.advance,ready_after_done R c hc]
  change (TM2.step (program c) (committing R e n)).getD (committing R e n) = _
  change (TM2.step (program c) ⟨some (if R e n then .accept else .reject),none,
    K'.elim (trList [candidate R e n,test R e n]) [] [] []⟩).getD _ = _
  rw [commit_step]
  rfl

theorem comparison_silent (hc : CodeCorrect R c) (e n j : Nat)
    (h : j < evalTime R c hc e n + 1) :
    ¬ (system c).BeepFrom (prepared c e n) j := by
  exact advance_silent c _ _ _ (evalTime_correct R c hc e n) j (by omega)

theorem commit_beep (hc : CodeCorrect R c) (e n : Nat) :
    (system c).BeepFrom (prepared c e n) (evalTime R c hc e n + 1) ↔ R e n = false := by
  unfold EventSystem.BeepFrom
  rw [ready_after_done R c hc]
  cases h : R e n <;> simp [system,committing,flag,h]

def Rel : Controller.State → Conf → Prop
  | .startup, x => x = initial
  | .testing e n, x => x = prepared c e n

noncomputable def duration (hc : CodeCorrect R c) : Controller.State → Conf → Nat
  | .startup, _ => 1
  | .testing e n, _ => evalTime R c hc e n + 2

/-- Each controller step is implemented by a finite positive segment of the
looping TM2 program, with exactly the corresponding event word. -/
noncomputable def simulation (hc : CodeCorrect R c) :
    SegmentSimulation (Controller.system R 0) (system c) where
  Rel := Rel c
  initial := rfl
  duration := duration R c hc
  positive := by
    intro state x h
    cases state <;> simp [duration]
  next := by
    intro state x h
    cases state with
    | startup =>
      subst x
      change (system c).advance initial 1 = prepared c 0 0
      change (TM2.step (program c) initial).getD initial = _
      rw [startup_step]
      rfl
    | testing e n =>
      subst x
      have hh := ready_after_commit R c hc e n
      cases hr : R e n <;>
        simpa [Controller.system,Controller.step,Rel,duration,candidate,test,hr] using hh
  event_iff := by
    intro state x h
    cases state with
    | startup =>
      subst x
      simp only [Controller.system,Controller.step,true_iff]
      refine ⟨0,by simp [duration],?_⟩
      simp [EventSystem.BeepFrom,EventSystem.advance,system,initial,flag]
    | testing e n =>
      subst x
      cases hr : R e n with
      | false =>
        simp only [Controller.system,Controller.step,hr,Bool.false_eq_true,↓reduceIte,true_iff]
        refine ⟨evalTime R c hc e n+1,by simp [duration],?_⟩
        exact (commit_beep R c hc e n).2 hr
      | true =>
        simp only [Controller.system,Controller.step,hr,↓reduceIte,Bool.false_eq_true,false_iff]
        rintro ⟨j,hj,hb⟩
        change j < evalTime R c hc e n + 2 at hj
        by_cases hlt : j < evalTime R c hc e n + 1
        · exact comparison_silent R c hc e n j hlt hb
        · have he : j = evalTime R c hc e n + 1 := by omega
          subst j
          have hf := (commit_beep R c hc e n).1 hb
          simp [hr] at hf
  event_unique := by
    intro state x h j k hj hk hjb hkb
    cases state with
    | startup => simp [duration] at hj hk; omega
    | testing e n =>
      subst x
      change j < evalTime R c hc e n + 2 at hj
      change k < evalTime R c hc e n + 2 at hk
      have hjn : ¬ j < evalTime R c hc e n + 1 := by
        intro hh; exact comparison_silent R c hc e n j hh hjb
      have hkn : ¬ k < evalTime R c hc e n + 1 := by
        intro hh; exact comparison_silent R c hc e n k hh hkb
      omega

theorem silent_iff_good (hc : CodeCorrect R c) :
    (system c).EventuallySilent ↔ ∃ e, Controller.Good R e :=
  ControllerRefinement.zero_start_target_silent_iff_good R (system c)
    (simulation R c hc).toEventRefinement

/-- A computable predicate has one fixed looping TM2 controller; no
unbounded Lean predicate occurs in that controller's transition program. -/
theorem exists_controller (hR : Computable₂ R) :
    ∃ c : Code, CodeCorrect R c ∧
      ((system c).EventuallySilent ↔ ∃ e, Controller.Good R e) := by
  obtain ⟨c,hc⟩ := has_update_code R hR
  exact ⟨c,hc,silent_iff_good R c hc⟩

end Shared.Beeping.ControllerTM2Refinement
