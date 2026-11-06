import Shared.Beeping.BinarySourceRefinement

/-! The same finite-table compiler from an explicitly supplied source tape.
This is a local execution interface; it does not claim a blank-start binary
machine initializes the supplied tape. -/
namespace Shared.Beeping.BinarySourceLoaded
open Shared.Beeping.Machines
open Shared.Beeping.ComparisonAlphabetBits
open Shared.Beeping.BinarySourceCompiler Shared.Beeping.BinarySourceRefinement

def sourceFrom {m : Nat} (tab : SourceTable m) (initial : SourceConfig m) : EventSystem (SourceConfig m) :=
  ⟨initial,sourceStep tab⟩

def binaryFrom {m : Nat} (tab : SourceTable m) (start : Fin m) (initial : SourceConfig m) :
    EventSystem (Config (Total m)) :=
  ⟨begin initial.state (binaryTape initial.tape) (13*initial.head),(machine tab start).step⟩

theorem advance_eq_of_step {α : Type} (A B : EventSystem α) (h : A.step = B.step)
    (c : α) (k : Nat) : A.advance c k = B.advance c k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [EventSystem.advance,ih,h]

theorem advance_eq {m : Nat} (tab : SourceTable m) (start : Fin m) (initial : SourceConfig m)
    (c : Config (Total m)) (k : Nat) :
    (binaryFrom tab start initial).advance c k = (machine tab start).system.advance c k := by
  apply advance_eq_of_step
  rfl

theorem beepFrom_eq {m : Nat} (tab : SourceTable m) (start : Fin m) (initial : SourceConfig m)
    (c : Config (Total m)) (k : Nat) :
    (binaryFrom tab start initial).BeepFrom c k ↔ (machine tab start).system.BeepFrom c k := by
  change ((machine tab start).step ((binaryFrom tab start initial).advance c k)).2 = true ↔
    ((machine tab start).step ((machine tab start).system.advance c k)).2 = true
  rw [advance_eq]

/-- Starting with a related loaded tape changes neither the finite segment
bounds nor the event-preserving progress proof. -/
def simulation {m : Nat} (tab : SourceTable m) (start : Fin m) (initial : SourceConfig m) :
    SegmentSimulation (sourceFrom tab initial) (binaryFrom tab start initial) where
  Rel := Rel
  initial := rfl
  duration := fun c _ => BinarySourceRefinement.duration tab c
  positive := by intro c d h; exact duration_positive tab c
  next := by
    intro c d h
    subst d
    rw [advance_eq]
    exact macro_next tab start c
  event_iff := by
    intro c d h
    subst d
    change (selected tab c.state (c.tape c.head)).beep = true ↔ _
    constructor
    · intro hb
      refine ⟨13,duration_after_event tab c,?_⟩
      apply (beepFrom_eq tab start initial _ _).2
      exact (macro_trace tab start c 13 (duration_after_event tab c)).2 ⟨rfl,hb⟩
    · rintro ⟨k,hk,hb⟩
      have hb' := (beepFrom_eq tab start initial _ _).1 hb
      exact ((macro_trace tab start c k hk).1 hb').2
  event_unique := by
    intro c d h j k hj hk hjb hkb
    subst d
    have hjb' := (beepFrom_eq tab start initial _ _).1 hjb
    have hkb' := (beepFrom_eq tab start initial _ _).1 hkb
    have hj' := ((macro_trace tab start c j hj).1 hjb').1
    have hk' := ((macro_trace tab start c k hk).1 hkb').1
    omega

theorem eventuallySilent_iff {m : Nat} (tab : SourceTable m) (start : Fin m) (initial : SourceConfig m) :
    (binaryFrom tab start initial).EventuallySilent ↔ (sourceFrom tab initial).EventuallySilent :=
  (simulation tab start initial).toEventRefinement.eventuallySilent_iff.symm

theorem infinitelyManyBeeps_iff {m : Nat} (tab : SourceTable m) (start : Fin m) (initial : SourceConfig m) :
    (binaryFrom tab start initial).InfinitelyManyBeeps ↔ (sourceFrom tab initial).InfinitelyManyBeeps :=
  (simulation tab start initial).toEventRefinement.infinitelyManyBeeps_iff.symm

end Shared.Beeping.BinarySourceLoaded
