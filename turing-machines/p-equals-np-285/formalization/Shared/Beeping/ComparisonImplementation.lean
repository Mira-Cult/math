import Shared.Beeping.ControllerRefinement
import Shared.Beeping.Machines

/-!
A certificate interface for implementing the rejection controller on a
fixed finite binary machine. It requires a finite startup segment, a finite
silent comparison segment, a finite-state Boolean result, and one subsequent
commit transition whose beep and next boundary are correct. The comparison
predicate and the certificate are specifications; they are not installed as
oracles in the machine table.

No implementation is constructed here. In particular, input preparation,
code decoding, the SAT/reference evaluators, and proofs that their machine
implementations satisfy this interface remain separate obligations.
-/
namespace Shared.Beeping.ComparisonImplementation

open Shared.Beeping.Machines

variable {n : Nat} (R : Controller.Comparison) (e₀ : Nat) (M : Machine n)

structure Certificate where
  /-- The target is ready to evaluate `(e, k)` from this configuration. -/
  ready : Nat → Nat → Config n → Prop
  /-- Finite lookup table of designated result states; `none` is not a result. -/
  result : Vector (Option Bool) n
  /-- Logical duration witness, not a runtime operation of the target. -/
  comparisonSteps : Nat → Nat → Config n → Nat
  comparison_positive : ∀ e k c, ready e k c → 0 < comparisonSteps e k c
  comparison_correct : ∀ e k c, ready e k c →
    result[(M.system.advance c (comparisonSteps e k c)).state] = some (R e k)
  comparison_silent : ∀ e k c, ready e k c → ∀ j,
    j < comparisonSteps e k c → ¬ M.system.BeepFrom c j
  commit_event : ∀ e k c, ready e k c →
    (M.system.BeepFrom c (comparisonSteps e k c) ↔ R e k = false)
  commit_next : ∀ e k c, ready e k c →
    let c' := M.system.advance c (comparisonSteps e k c + 1)
    if R e k then ready e (k + 1) c' else ready (e + 1) 0 c'
  startupSteps : Nat
  startup_positive : 0 < startupSteps
  startup_ready : ready e₀ 0 (M.system.advance M.system.initial startupSteps)
  startup_event : ∃ j, j < startupSteps ∧ M.system.BeepFrom M.system.initial j
  startup_unique : ∀ j k, j < startupSteps → k < startupSteps →
    M.system.BeepFrom M.system.initial j → M.system.BeepFrom M.system.initial k → j = k

namespace Certificate

variable {R e₀ M} (cert : Certificate R e₀ M)

def Rel : Controller.State → Config n → Prop
  | .startup, c => c = M.system.initial
  | .testing e k, c => cert.ready e k c

def duration : Controller.State → Config n → Nat
  | .startup, _ => cert.startupSteps
  | .testing e k, c => cert.comparisonSteps e k c + 1

/-- The certificate supplies finite, silent, result-correct comparison
execution, followed by one correctly labelled commit transition. -/
theorem comparison_finishes {e k : Nat} {c : Config n} (h : cert.ready e k c) :
    ∃ d, 0 < d ∧
      cert.result[(M.system.advance c d).state] = some (R e k) ∧
      (∀ j, j < d → ¬ M.system.BeepFrom c j) ∧
      (M.system.BeepFrom c d ↔ R e k = false) ∧
      (if R e k then cert.ready e (k + 1) (M.system.advance c (d + 1))
       else cert.ready (e + 1) 0 (M.system.advance c (d + 1))) := by
  refine ⟨cert.comparisonSteps e k c, cert.comparison_positive e k c h,
    cert.comparison_correct e k c h, cert.comparison_silent e k c h,
    cert.commit_event e k c h, cert.commit_next e k c h⟩

/-- Every supplied certificate yields the progress-sensitive local simulation. -/
def toSegmentSimulation : SegmentSimulation (Controller.system R e₀) M.system where
  Rel := cert.Rel
  initial := rfl
  duration := cert.duration
  positive := by
    intro state c h
    cases state with
    | startup => exact cert.startup_positive
    | testing e k =>
      have hp := cert.comparison_positive e k c h
      change 0 < cert.comparisonSteps e k c + 1
      omega
  next := by
    intro state c h
    cases state with
    | startup =>
      subst c
      simpa [Controller.system, Controller.step, Rel, duration] using cert.startup_ready
    | testing e k =>
      have hn := cert.commit_next e k c h
      cases hr : R e k <;>
        simpa [Controller.system, Controller.step, Rel, duration, hr] using hn
  event_iff := by
    intro state c h
    cases state with
    | startup =>
      subst c
      simp only [Controller.system, Controller.step, true_iff]
      simpa [duration] using cert.startup_event
    | testing e k =>
      have hc := cert.commit_event e k c h
      simp only [Controller.system, Controller.step]
      cases hr : R e k with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, true_iff]
        refine ⟨cert.comparisonSteps e k c, ?_, ?_⟩
        · simp [duration]
        · exact hc.2 hr
      | true =>
        simp only [↓reduceIte, Bool.false_eq_true, false_iff]
        rintro ⟨j, hj, hb⟩
        change j < cert.comparisonSteps e k c + 1 at hj
        by_cases hlt : j < cert.comparisonSteps e k c
        · exact cert.comparison_silent e k c h j hlt hb
        · have heq : j = cert.comparisonSteps e k c := by omega
          subst j
          have hf := hc.1 hb
          simp [hr] at hf
  event_unique := by
    intro state c h j k hj hk hjb hkb
    cases state with
    | startup =>
      subst c
      exact cert.startup_unique j k hj hk hjb hkb
    | testing e test =>
      change j < cert.comparisonSteps e test c + 1 at hj
      change k < cert.comparisonSteps e test c + 1 at hk
      have hjn : ¬ j < cert.comparisonSteps e test c := by
        intro hlt
        exact cert.comparison_silent e test c h j hlt hjb
      have hkn : ¬ k < cert.comparisonSteps e test c := by
        intro hlt
        exact cert.comparison_silent e test c h k hlt hkb
      omega

/-- A certified finite comparison implementation transfers the abstract
controller equivalence to the concrete total machine. -/
theorem eventuallySilent_iff_good (cert : Certificate R e₀ M) :
    M.system.EventuallySilent ↔ ∃ e, e₀ ≤ e ∧ Controller.Good R e :=
  ControllerRefinement.local_target_silent_iff_good R e₀ M.system cert.toSegmentSimulation

/-- In particular, no certified all-bad controller can become silent by
stalling inside a comparison. -/
theorem all_bad_infinitely_many_beeps (cert : Certificate R e₀ M)
    (hbad : ∀ e, e₀ ≤ e → ¬ Controller.Good R e) :
    M.system.InfinitelyManyBeeps :=
  cert.toSegmentSimulation.toEventRefinement.infinitelyManyBeeps_iff.1
    (Controller.all_bad_infinitely_many_beeps R e₀ hbad)

end Certificate
end Shared.Beeping.ComparisonImplementation
