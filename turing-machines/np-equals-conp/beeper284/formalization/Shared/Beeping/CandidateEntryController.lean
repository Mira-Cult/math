import Shared.Beeping.ControllerRefinement

/-!
An atomic-comparison controller with a distinct beep at entry to each
candidate. A rejected comparison takes a silent transition to the next
candidate's entry state, which emits on its next transition. In contrast,
`Controller` emits the next candidate's beep on the failed comparison.

The simulation below accounts for this difference with one target step per
successful comparison and two per failed comparison. It does not establish
that any physical machine implements these atomic comparisons.
-/
namespace Shared.Beeping.CandidateEntryController

inductive State where
  | entry (candidate : Nat)
  | testing (candidate test : Nat)
  deriving DecidableEq, Repr

def step (R : Controller.Comparison) : State → State × Bool
  | .entry e => (.testing e 0, true)
  | .testing e n =>
      if R e n then (.testing e (n + 1), false)
      else (.entry (e + 1), false)

def system (R : Controller.Comparison) (e₀ : Nat) : EventSystem State where
  initial := .entry e₀
  step := step R

/-- Entry is a real transition, including the first beep. -/
@[simp] theorem initial_beep (R : Controller.Comparison) (e₀ : Nat) :
    (system R e₀).BeepAt 0 := rfl

inductive Rel (e₀ : Nat) : Controller.State → State → Prop where
  | startup : Rel e₀ .startup (.entry e₀)
  | testing (e n : Nat) : Rel e₀ (.testing e n) (.testing e n)

/-- A failed comparison is followed by the next entry's explicit beep. -/
def duration (R : Controller.Comparison) : Controller.State → State → Nat
  | .testing e n, .testing _ _ => if R e n then 1 else 2
  | _, _ => 1

def simulation (R : Controller.Comparison) (e₀ : Nat) :
    SegmentSimulation (Controller.system R e₀) (system R e₀) where
  Rel := Rel e₀
  initial := Rel.startup
  duration := duration R
  positive := by
    intro s t h
    cases h with
    | startup => simp [duration]
    | testing e n => simp [duration]; split <;> omega
  next := by
    intro s t h
    cases h with
    | startup =>
      simpa [duration, Controller.system, Controller.step, system, step,
        EventSystem.advance] using (Rel.testing (e₀ := e₀) e₀ 0)
    | testing e n =>
      cases hr : R e n <;>
        simp [duration, Controller.system, Controller.step, system, step,
          EventSystem.advance, hr, Rel.testing]
  event_iff := by
    intro s t h
    cases h with
    | startup =>
      simp [duration, Controller.system, Controller.step, system, step,
        EventSystem.BeepFrom, EventSystem.advance]
    | testing e n =>
      cases hr : R e n with
      | false =>
        simp [duration, Controller.system, Controller.step, system, hr]
        exact ⟨1, by decide, by simp [EventSystem.BeepFrom, EventSystem.advance, step, hr]⟩
      | true =>
        simp [duration, Controller.system, Controller.step, system, hr]
        intro hbeep
        simp [EventSystem.BeepFrom, EventSystem.advance, step, hr] at hbeep
  event_unique := by
    intro s t h j k hj hk hjb hkb
    cases h with
    | startup =>
      simp [duration] at hj hk
      omega
    | testing e n =>
      cases hr : R e n with
      | false =>
        simp only [duration, hr, Bool.false_eq_true, ↓reduceIte] at hj hk
        have hj' : j = 1 := by
          by_cases hzero : j = 0
          · subst j
            simp [system, step, EventSystem.BeepFrom, EventSystem.advance, hr] at hjb
          · omega
        have hk' : k = 1 := by
          by_cases hzero : k = 0
          · subst k
            simp [system, step, EventSystem.BeepFrom, EventSystem.advance, hr] at hkb
          · omega
        omega
      | true =>
        simp [duration, hr] at hj hk
        omega

theorem eventuallySilent_iff (R : Controller.Comparison) (e₀ : Nat) :
    (system R e₀).EventuallySilent ↔ ∃ e, e₀ ≤ e ∧ Controller.Good R e :=
  ControllerRefinement.local_target_silent_iff_good R e₀ (system R e₀)
    (simulation R e₀)

theorem infinitelyManyBeeps_iff (R : Controller.Comparison) (e₀ : Nat) :
    (Controller.system R e₀).InfinitelyManyBeeps ↔
      (system R e₀).InfinitelyManyBeeps :=
  (simulation R e₀).toEventRefinement.infinitelyManyBeeps_iff

end Shared.Beeping.CandidateEntryController
