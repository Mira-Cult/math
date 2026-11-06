import Shared.Beeping.WordEventCoverage

/-! Ordered-word simulations may have a paid finite silent startup. Dropping
that finite prefix preserves eventual silence and infinite beeping. -/
namespace PASoundness.WordEventCoverageBoot
open Shared.Beeping

def shifted {C A : Type} (W : WordEventSystem C A) (k : Nat) : WordEventSystem C A where
  initial := W.run k
  step := W.step

@[simp] theorem shifted_advance {C A : Type} (W : WordEventSystem C A) (k : Nat) (c : C) (n : Nat) :
    (shifted W k).advance c n = W.advance c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (W.step ((shifted W k).advance c n)).1 = (W.step (W.advance c n)).1
    rw [ih]

@[simp] theorem shifted_wordFrom {C A : Type} (W : WordEventSystem C A) (k : Nat) (c : C) (n : Nat) :
    (shifted W k).wordFrom c n = W.wordFrom c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (shifted W k).wordFrom c n ++ (W.step ((shifted W k).advance c n)).2 =
      W.wordFrom c n ++ (W.step (W.advance c n)).2
    rw [ih,shifted_advance]

theorem shifted_beepAt {C A : Type} (W : WordEventSystem C A) (k t : Nat) :
    (shifted W k).erase.BeepAt t ↔ W.erase.BeepAt (k+t) := by
  rw [WordEventSystem.erase_beep_iff,WordEventSystem.erase_beep_iff,WordEventSystem.run_add]
  change (W.step ((shifted W k).run t)).2 ≠ [] ↔
    (W.step (W.advance (W.run k) t)).2 ≠ []
  have hrun : (shifted W k).run t = W.advance (W.run k) t := by
    change (shifted W k).advance (W.run k) t = _
    exact shifted_advance W k (W.run k) t
  rw [hrun]

theorem shifted_eventuallySilent_iff {C A : Type} (W : WordEventSystem C A) (k : Nat) :
    W.erase.EventuallySilent ↔ (shifted W k).erase.EventuallySilent := by
  rw [EventSystem.eventuallySilent_iff_shift W.erase k]
  simp only [EventSystem.EventuallySilent,shifted_beepAt]

/-- Rebase a local simulation after its actual paid startup, preserving the
same transition relation, positive costs and exact output words. -/
def shiftedSimulation {S T A : Type} {source : WordEventSystem S A} {target : WordEventSystem T A}
    (r : PASoundness.SegmentSimulation source target) :
    PASoundness.SegmentSimulation source (shifted target r.startup) where
  Rel := r.Rel
  startup := 0
  initial := by
    change r.Rel source.initial (target.run r.startup)
    exact r.initial
  startup_silent := rfl
  duration := r.duration
  positive := r.positive
  next := by
    intro s t h
    simpa using r.next s t h
  word_eq := by
    intro s t h
    simpa using r.word_eq s t h

/-- A finite silent startup is fully accounted for and need not have zero
length. All later target transitions lie in positive finite source segments. -/
theorem eventuallySilent_iff {S T A : Type} {source : WordEventSystem S A} {target : WordEventSystem T A}
    (r : PASoundness.SegmentSimulation source target) :
    source.erase.EventuallySilent ↔ target.erase.EventuallySilent := by
  have h := WordEventCoverage.eventuallySilent_iff (shiftedSimulation r) rfl
  exact h.trans (shifted_eventuallySilent_iff target r.startup).symm

theorem infinitelyManyBeeps_iff {S T A : Type} {source : WordEventSystem S A} {target : WordEventSystem T A}
    (r : PASoundness.SegmentSimulation source target) :
    source.erase.InfinitelyManyBeeps ↔ target.erase.InfinitelyManyBeeps := by
  rw [← EventSystem.not_eventuallySilent_iff_infinitelyMany,
    ← EventSystem.not_eventuallySilent_iff_infinitelyMany,eventuallySilent_iff r]

end PASoundness.WordEventCoverageBoot
