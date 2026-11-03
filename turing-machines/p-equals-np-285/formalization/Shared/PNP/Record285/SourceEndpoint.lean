import Shared.PNP.Record285.Source
import Shared.Beeping.Refinement

/-! Source-controller composition. This file concerns the abstract controller
only, not the Python AST, physical table, or canonical complexity classes. -/
namespace Shared.PNP.Record285.Source
open Shared.Beeping

/-- A candidate that is not uniformly correct has a concrete bad input. -/
theorem notGood_has_bad (program exponent : Nat) (h : ¬ GoodCandidate program exponent) :
    ∃ n remaining, remaining < 2^n ∧
      mismatch program exponent n (2^n) remaining = true := by
  classical
  apply Classical.byContradiction
  intro hnone
  apply h
  intro n remaining hbound
  cases hm : mismatch program exponent n (2^n) remaining with
  | false => rfl
  | true => exact False.elim (hnone ⟨n,remaining,hbound,hm⟩)

/-- Every nonempty set of failure times has a least element. -/
theorem scan_first_failure (program exponent : Nat)
    (hexists : ∃ t, Failure ((scanSystem program exponent).run t)) :
    ∃ t, Failure ((scanSystem program exponent).run t) ∧
      ∀ j, j < t → ¬ Failure ((scanSystem program exponent).run j) := by
  classical
  obtain ⟨n,hn⟩ := hexists
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hearlier : ∃ j, j < n ∧ Failure ((scanSystem program exponent).run j)
    · obtain ⟨j,hj,hf⟩ := hearlier
      exact ih j hj hf
    · refine ⟨n,hn,?_⟩
      intro j hj hf
      exact hearlier ⟨j,hj,hf⟩

/-- At the first failure, the original candidate and exponent are still active. -/
theorem scan_first_failure_candidate (program exponent : Nat)
    (hexists : ∃ t, Failure ((scanSystem program exponent).run t)) :
    ∃ t, Failure ((scanSystem program exponent).run t) ∧
      ((scanSystem program exponent).run t).program = program ∧
      ((scanSystem program exponent).run t).exponent = exponent := by
  obtain ⟨t,hfail,hfirst⟩ := scan_first_failure program exponent hexists
  have hprefix : ∀ j, j < t →
      let s := (scanSystem program exponent).run j
      s.phase = .compare → mismatch s.program s.exponent s.n s.radix s.remaining = false := by
    intro j hj
    dsimp only
    intro hp
    exact noFailure_mismatch _ hp (hfirst j hj)
  have hs := scan_prefix_progress program exponent t hprefix
  exact ⟨t,hfail,hs.1,hs.2.1⟩

/-- Starting at a begin phase in the real abstract controller gives exactly the
corresponding fresh candidate scan after the begin event. -/
theorem controller_from_begin (start : Nat) (s : SearchState)
    (hstate : controller.run start = s) (hphase : s.phase = .begin) (j : Nat) :
    controller.run (start + 1 + j) = (scanSystem s.program s.exponent).run j := by
  induction j with
  | zero =>
    change (controllerStep (controller.run start)).1 = (scanSystem s.program s.exponent).initial
    rw [hstate]
    simp [controllerStep, hphase, scanSystem]
  | succ j ih =>
    rw [Nat.add_succ, EventSystem.run_succ, EventSystem.run_succ, ih]
    rfl


def candidateAt (i : Nat) : Nat × Nat := candidateAfter i (0,1)

def AtBegin (i t : Nat) : Prop :=
  (controller.run t).phase = .begin ∧
  (controller.run t).program = (candidateAt i).1 ∧
  (controller.run t).exponent = (candidateAt i).2

/-- If all earlier candidates fail, the given candidate is reached after a
finite number of source steps. -/
theorem reachCandidate (i : Nat)
    (hbad : ∀ j, j < i → ¬ GoodCandidate (candidateAt j).1 (candidateAt j).2) :
    ∃ t, i ≤ t ∧ AtBegin i t := by
  induction i with
  | zero =>
    refine ⟨0, by omega, ?_⟩
    simp [AtBegin, candidateAt, candidateAfter, controller, EventSystem.run]
  | succ i ih =>
    have hprev : ∀ j, j < i → ¬ GoodCandidate (candidateAt j).1 (candidateAt j).2 := by
      intro j hj
      exact hbad j (by omega)
    obtain ⟨t, ht, hphase, hp, he⟩ := ih hprev
    have hnot : ¬ GoodCandidate (controller.run t).program (controller.run t).exponent := by
      simpa [hp, he] using hbad i (by omega)
    obtain ⟨n,w,hw,hwrong⟩ := notGood_has_bad _ _ hnot
    obtain ⟨j,_,hfail⟩ := scan_bad_fails (controller.run t).program
      (controller.run t).exponent n w hw hwrong
    obtain ⟨m,hfirst,hprogram,hexponent⟩ := scan_first_failure_candidate
      (controller.run t).program (controller.run t).exponent ⟨j,hfail⟩
    refine ⟨t+1+m+1, by omega, ?_⟩
    have hrun : controller.run (t+1+m+1) =
        (controllerStep ((scanSystem (controller.run t).program (controller.run t).exponent).run m)).1 := by
      rw [EventSystem.run_succ, controller_from_begin t (controller.run t) rfl hphase m]
      rfl
    unfold AtBegin
    rw [hrun]
    rcases hfirst with ⟨hfphase,hwrong'⟩
    simp only [controllerStep, hfphase, hwrong', ↓reduceIte]
    rw [hprogram, hexponent, hp, he]
    simp [candidateAt, candidateAfter]


theorem candidateAt_positive (i : Nat) : 0 < (candidateAt i).2 := by
  cases i with
  | zero => decide
  | succ i => exact advanceCandidate_positive _ _

/-- Reaching a good candidate gives continued silent comparisons. -/
theorem good_begin_silent (i t : Nat) (hat : AtBegin i t)
    (hgood : GoodCandidate (candidateAt i).1 (candidateAt i).2) :
    controller.EventuallySilent := by
  rcases hat with ⟨hphase,hp,he⟩
  have hg : GoodCandidate (controller.run t).program (controller.run t).exponent := by
    simpa [hp,he] using hgood
  refine ⟨t+1, ?_⟩
  intro u hu hbeep
  have hu' : t+1+(u-(t+1)) = u := by omega
  rw [← hu'] at hbeep
  change (controllerStep (controller.run (t+1+(u-(t+1))))).2 = true at hbeep
  rw [controller_from_begin t (controller.run t) rfl hphase] at hbeep
  exact scan_good_silent _ _ hg _ hbeep

/-- Some good candidate at a given rank is enough for eventual source silence;
earlier good candidates are handled without assuming a least-index operator. -/
theorem good_at_silent (i : Nat)
    (hgood : GoodCandidate (candidateAt i).1 (candidateAt i).2) :
    controller.EventuallySilent := by
  classical
  induction i using Nat.strongRecOn with
  | ind i ih =>
    by_cases hearlier : ∃ j, j < i ∧ GoodCandidate (candidateAt j).1 (candidateAt j).2
    · obtain ⟨j,hj,hg⟩ := hearlier
      exact ih j hj hg
    · have hbad : ∀ j, j < i → ¬ GoodCandidate (candidateAt j).1 (candidateAt j).2 := by
        intro j hj hg
        exact hearlier ⟨j,hj,hg⟩
      obtain ⟨t,_,hat⟩ := reachCandidate i hbad
      exact good_begin_silent i t hat hgood

/-- The source controller has finitely many events exactly when some candidate
with a positive exponent agrees on every admissible input. This theorem says
nothing yet about canonical complexity classes or the literal tape machine. -/
theorem eventuallySilent_iff_goodCandidate :
    controller.EventuallySilent ↔
      ∃ program exponent, 0 < exponent ∧ GoodCandidate program exponent := by
  classical
  constructor
  · intro hquiet
    apply Classical.byContradiction
    intro hnone
    obtain ⟨T,hT⟩ := hquiet
    have hbad : ∀ j, j < T → ¬ GoodCandidate (candidateAt j).1 (candidateAt j).2 := by
      intro j _ hg
      exact hnone ⟨(candidateAt j).1,(candidateAt j).2,candidateAt_positive j,hg⟩
    obtain ⟨t,ht,hat⟩ := reachCandidate T hbad
    have hbeep : controller.BeepAt t := by
      change (controllerStep (controller.run t)).2 = true
      exact (controllerStep_beep _).2 hat.1
    exact hT t ht hbeep
  · rintro ⟨program,exponent,hpos,hgood⟩
    let i := triangle (program + exponent - 1) + (exponent - 1)
    have hi : candidateAt i = (program,exponent) := candidateAfter_covers program exponent hpos
    apply good_at_silent i
    simpa [hi] using hgood


/-- Polarity of the abstract source event stream. -/
theorem infinitelyMany_iff_no_goodCandidate :
    controller.InfinitelyManyBeeps ↔
      ¬ ∃ program exponent, 0 < exponent ∧ GoodCandidate program exponent := by
  rw [← EventSystem.not_eventuallySilent_iff_infinitelyMany,
    eventuallySilent_iff_goodCandidate]

theorem finiteEvents_iff_goodCandidate :
    controller.FiniteEventTimes ↔
      ∃ program exponent, 0 < exponent ∧ GoodCandidate program exponent := by
  rw [← EventSystem.eventuallySilent_iff_finiteEventTimes,
    eventuallySilent_iff_goodCandidate]

end Shared.PNP.Record285.Source
