import Shared.Beeping.Controller
import Shared.Beeping.Refinement

/-!
The controller equivalence can be transferred to a target once an actual
refinement is supplied. The candidate/class characterization is an explicit
hypothesis and is not a complexity-theoretic theorem in this module.
-/
namespace Shared.Beeping.ControllerRefinement

variable {T : Type} (R : Controller.Comparison) (e₀ : Nat) (target : EventSystem T)

theorem target_silent_iff_good
    (r : EventRefinement (Controller.system R e₀) target) :
    target.EventuallySilent ↔ ∃ e, e₀ ≤ e ∧ Controller.Good R e := by
  calc
    target.EventuallySilent ↔ (Controller.system R e₀).EventuallySilent :=
      r.eventuallySilent_iff.symm
    _ ↔ ∃ e, e₀ ≤ e ∧ Controller.Good R e :=
      Controller.eventuallySilent_iff_exists_good R e₀

theorem target_silent_iff_of_characterization (P : Prop)
    (r : EventRefinement (Controller.system R e₀) target)
    (h : (∃ e, e₀ ≤ e ∧ Controller.Good R e) ↔ P) :
    target.EventuallySilent ↔ P :=
  (target_silent_iff_good R e₀ target r).trans h

theorem local_target_silent_iff_good
    (s : SegmentSimulation (Controller.system R e₀) target) :
    target.EventuallySilent ↔ ∃ e, e₀ ≤ e ∧ Controller.Good R e :=
  target_silent_iff_good R e₀ target s.toEventRefinement

theorem zero_start_target_silent_iff_good
    (r : EventRefinement (Controller.system R 0) target) :
    target.EventuallySilent ↔ ∃ e, Controller.Good R e := by
  simpa using target_silent_iff_good R 0 target r

end Shared.Beeping.ControllerRefinement
