import Shared.Beeping.BinarySourceMovement

/-! An event-preserving, progress-sensitive binary compiler for the explicit
finite source-table model. This does not yet extract an actual comparator
source table or initialize a comparator program on its tape. -/
namespace Shared.Beeping.BinarySourceRefinement
open Shared.Beeping.Machines
open Shared.Beeping.ComparisonAlphabetBits Shared.Beeping.ComparisonSingleTape
open Shared.Beeping.BinarySourceCompiler Shared.Beeping.BinarySourceMovement

structure SourceConfig (m : Nat) where
  state : Fin m
  head : Int
  tape : Int → Alphabet

def sourceStep {m : Nat} (tab : SourceTable m) (c : SourceConfig m) : SourceConfig m × Bool :=
  let r := selected tab c.state (c.tape c.head)
  (match r.action with
   | .write a => ⟨r.next,c.head,Function.update c.tape c.head a⟩
   | .left => ⟨r.next,c.head-1,c.tape⟩
   | .right => ⟨r.next,c.head+1,c.tape⟩,r.beep)

def sourceSystem {m : Nat} (tab : SourceTable m) (start : Fin m) : EventSystem (SourceConfig m) where
  initial := ⟨start,0,fun _ => default⟩
  step := sourceStep tab

def duration {m : Nat} (tab : SourceTable m) (c : SourceConfig m) : Nat :=
  match (selected tab c.state (c.tape c.head)).action with
  | .write _ => 28 | .left => 39 | .right => 15

def Rel {m : Nat} (c : SourceConfig m) (d : Config (Total m)) : Prop :=
  d = begin c.state (binaryTape c.tape) (13*c.head)

theorem duration_positive {m : Nat} (tab : SourceTable m) (c : SourceConfig m) : 0 < duration tab c := by
  unfold duration
  cases (selected tab c.state (c.tape c.head)).action <;> simp

theorem duration_after_event {m : Nat} (tab : SourceTable m) (c : SourceConfig m) : 13 < duration tab c := by
  unfold duration
  cases (selected tab c.state (c.tape c.head)).action <;> simp

/-- The full binary segment reaches the next source configuration, including
its destination state, tape, and aligned head. -/
theorem macro_next {m : Nat} (tab : SourceTable m) (start : Fin m) (c : SourceConfig m) :
    Rel (sourceStep tab c).1
      ((machine tab start).system.advance (begin c.state (binaryTape c.tape) (13*c.head)) (duration tab c)) := by
  cases hact : (selected tab c.state (c.tape c.head)).action with
  | write a =>
    have h := complete_write tab start c.state c.tape c.head a hact
    simpa [Rel,sourceStep,duration,hact,begin,scanConfig,BinaryBlockScan.begin,ready] using h
  | left =>
    have h := complete_left tab start c.state c.tape c.head hact
    simpa [Rel,sourceStep,duration,hact,begin,scanConfig,BinaryBlockScan.begin,ready,Int.mul_sub] using h
  | right =>
    have h := complete_right tab start c.state c.tape c.head hact
    simpa [Rel,sourceStep,duration,hact,begin,scanConfig,BinaryBlockScan.begin,ready,Int.mul_add] using h

/-- The only possible event of each source-step segment is the fixed source
row's flag at the thirteenth transition. -/
theorem macro_trace {m : Nat} (tab : SourceTable m) (start : Fin m) (c : SourceConfig m)
    (k : Nat) (hk : k < duration tab c) :
    (machine tab start).system.BeepFrom (begin c.state (binaryTape c.tape) (13*c.head)) k ↔
      k = 13 ∧ (selected tab c.state (c.tape c.head)).beep = true := by
  cases hact : (selected tab c.state (c.tape c.head)).action with
  | write a =>
    exact write_trace tab start c.state c.tape c.head a hact k (by simpa [duration,hact] using hk)
  | left =>
    exact left_trace tab start c.state c.tape c.head hact k (by simpa [duration,hact] using hk)
  | right =>
    exact right_trace tab start c.state c.tape c.head hact k (by simpa [duration,hact] using hk)

/-- The literal finite source table compiles to the actual total binary model,
with positive segments and exactly matching event words. -/
def simulation {m : Nat} (tab : SourceTable m) (start : Fin m) :
    SegmentSimulation (sourceSystem tab start) (machine tab start).system where
  Rel := Rel
  initial := by
    change (machine tab start).initial = begin start (binaryTape (fun _ => default)) 0
    have he : binaryTape (fun _ => (default : Alphabet)) = (fun _ => false) := by
      funext i
      exact blankTape i
    simp [Machine.initial,machine,begin,scanConfig,BinaryBlockScan.begin,ready,he]
  duration := fun c _ => duration tab c
  positive := by intro c d h; exact duration_positive tab c
  next := by
    intro c d h
    subst d
    exact macro_next tab start c
  event_iff := by
    intro c d h
    subst d
    change (selected tab c.state (c.tape c.head)).beep = true ↔ _
    constructor
    · intro hb
      refine ⟨13,duration_after_event tab c,?_⟩
      exact (macro_trace tab start c 13 (duration_after_event tab c)).2 ⟨rfl,hb⟩
    · rintro ⟨k,hk,hb⟩
      exact ((macro_trace tab start c k hk).1 hb).2
  event_unique := by
    intro c d h j k hj hk hjb hkb
    subst d
    have hj' := ((macro_trace tab start c j hj).1 hjb).1
    have hk' := ((macro_trace tab start c k hk).1 hkb).1
    omega

/-- No target-only silent stall can change eventual silence or infinite
beeping: the local simulation covers the entire infinite binary run. -/
theorem eventuallySilent_iff {m : Nat} (tab : SourceTable m) (start : Fin m) :
    (machine tab start).system.EventuallySilent ↔ (sourceSystem tab start).EventuallySilent :=
  (simulation tab start).toEventRefinement.eventuallySilent_iff.symm

theorem infinitelyManyBeeps_iff {m : Nat} (tab : SourceTable m) (start : Fin m) :
    (machine tab start).system.InfinitelyManyBeeps ↔ (sourceSystem tab start).InfinitelyManyBeeps :=
  (simulation tab start).toEventRefinement.infinitelyManyBeeps_iff.symm

namespace Fixtures

def one : Fin 1 := ⟨0,by decide⟩

def constant (b : Bool) : SourceTable 1 :=
  Vector.ofFn fun _ => Vector.ofFn fun _ => ⟨one,.right,b⟩

theorem selected_constant (b : Bool) (q : Fin 1) (a : Alphabet) :
    selected (constant b) q a = ⟨one,.right,b⟩ := by
  change ((Vector.ofFn (fun _ : Fin 1 => Vector.ofFn (fun _ : Fin 8192 =>
    (⟨one,.right,b⟩ : SourceRow 1))))[q.val]).get (BinaryBlockWrite.wordOf a) = _
  rw [Vector.getElem_ofFn]
  change (Vector.ofFn (fun _ : Fin 8192 => (⟨one,.right,b⟩ : SourceRow 1)))[(BinaryBlockWrite.wordOf a).val] = _
  rw [Vector.getElem_ofFn]

example : (machine (constant false) one).system.EventuallySilent := by
  apply (eventuallySilent_iff (constant false) one).2
  refine ⟨0, ?_⟩
  intro t _
  simp [EventSystem.BeepAt,sourceSystem,sourceStep,selected_constant]

example : (machine (constant true) one).system.InfinitelyManyBeeps := by
  apply (infinitelyManyBeeps_iff (constant true) one).2
  intro T
  refine ⟨T,le_rfl,?_⟩
  simp [EventSystem.BeepAt,sourceSystem,sourceStep,selected_constant]

end Fixtures

end Shared.Beeping.BinarySourceRefinement
