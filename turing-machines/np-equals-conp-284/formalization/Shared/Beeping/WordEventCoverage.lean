import Shared.Beeping.WordBridge
import Shared.Beeping.EventCoverage
import Mathlib.Tactic

/-! Positive finite ordered-word simulations preserve scalar eventual
silence and infinite beeping under event erasure. -/
namespace PASoundness.WordEventCoverage
open Shared.Beeping

/-- A finite emitted word is empty exactly when every transition in the
segment has an empty event word. -/
theorem wordFrom_eq_nil_iff {C A : Type} (W : WordEventSystem C A) (c : C) (n : Nat) :
    W.wordFrom c n = [] ↔ ∀ j < n, (W.step (W.advance c j)).2 = [] := by
  induction n with
  | zero => simp [WordEventSystem.wordFrom]
  | succ n ih =>
    simp only [WordEventSystem.wordFrom,List.append_eq_nil_iff,ih]
    constructor
    · rintro ⟨hp,hl⟩ j hj
      by_cases hn : j<n
      · exact hp j hn
      · have : j=n := by omega
        simpa [this] using hl
    · intro h
      exact ⟨fun j hj => h j (by omega),h n (by omega)⟩

theorem wordFrom_ne_nil_iff {C A : Type} (W : WordEventSystem C A) (c : C) (n : Nat) :
    W.wordFrom c n ≠ [] ↔ ∃ j < n, (W.step (W.advance c j)).2 ≠ [] := by
  classical
  change ¬ (W.wordFrom c n = []) ↔ _
  rw [wordFrom_eq_nil_iff]
  push_neg
  rfl

/-- A zero-startup ordered-word simulation covers every target event with the
source transition whose positive finite segment contains it. -/
def coverage {S T A : Type} {source : WordEventSystem S A} {target : WordEventSystem T A}
    (r : PASoundness.SegmentSimulation source target) (hstart : r.startup=0) :
    EventCoverage source.erase target.erase where
  boundary := r.boundary
  boundary_zero := by simpa [PASoundness.SegmentSimulation.boundary] using hstart
  progress := r.boundary_progress
  event_iff := by
    intro i
    have hevent (j : Nat) : target.erase.BeepAt (r.boundary i+j) ↔
        (target.step (target.advance (target.run (r.boundary i)) j)).2 ≠ [] := by
      rw [WordEventSystem.erase_beep_iff,WordEventSystem.run_add]
    have hword := r.word_eq _ _ (r.related_boundary i)
    have hnext : r.boundary (i+1) = r.boundary i +
        r.duration (source.run i) (target.run (r.boundary i)) := rfl
    rw [WordEventSystem.erase_beep_iff,← hword,wordFrom_ne_nil_iff]
    constructor
    · rintro ⟨j,hj,hb⟩
      refine ⟨r.boundary i+j,by omega,?_,(hevent j).2 hb⟩
      rw [hnext]
      omega
    · rintro ⟨t,hlo,hhi,hb⟩
      let j := t-r.boundary i
      have ht : t=r.boundary i+j := by dsimp [j]; omega
      refine ⟨j,?_,?_⟩
      · rw [hnext] at hhi
        dsimp [j]
        omega
      · rw [ht] at hb
        exact (hevent j).1 hb

theorem eventuallySilent_iff {S T A : Type} {source : WordEventSystem S A} {target : WordEventSystem T A}
    (r : PASoundness.SegmentSimulation source target) (hstart : r.startup=0) :
    source.erase.EventuallySilent ↔ target.erase.EventuallySilent :=
  (coverage r hstart).eventuallySilent_iff

theorem infinitelyManyBeeps_iff {S T A : Type} {source : WordEventSystem S A} {target : WordEventSystem T A}
    (r : PASoundness.SegmentSimulation source target) (hstart : r.startup=0) :
    source.erase.InfinitelyManyBeeps ↔ target.erase.InfinitelyManyBeeps :=
  (coverage r hstart).infinitelyManyBeeps_iff

end PASoundness.WordEventCoverage
