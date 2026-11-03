import Shared.Beeping.PostSourceRefinement

/-! Explicit obligations for binding a finite table to an external
post-Turing evaluator. This is a conditional theorem, not an extraction of
an arbitrary Lean function or a serialized comparator program. -/
namespace Shared.Beeping.PostTableBinding
open Turing
open Shared.Beeping.ComparisonSingleTape
open Shared.Beeping.BinarySourceCompiler
open Shared.Beeping.BinarySourceLoaded
open Shared.Beeping.PostSourceRefinement

variable {Λ : Type} [Inhabited Λ]

def statement : Action → TM0.Stmt Alphabet
  | .write a => .write a
  | .left => .move .left
  | .right => .move .right

/-- Every finite source row must match the actual external machine row and
flag for every alphabet symbol. No run-time query of the external function is
installed in the compiled binary table. -/
structure Binding (M : TM0.Machine Alphabet Λ) (flags : Λ → Alphabet → Bool)
    {m : Nat} (tab : SourceTable m) where
  state : Fin m → Λ
  row : ∀ q a, M (state q) a =
    some (state (selected tab q a).next,statement (selected tab q a).action)
  event : ∀ q a, flags (state q) a = (selected tab q a).beep

structure ExternalConfig where
  state : Λ
  tape : Tape Alphabet

def externalStep (M : TM0.Machine Alphabet Λ) (flags : Λ → Alphabet → Bool)
    (c : ExternalConfig (Λ := Λ)) : ExternalConfig (Λ := Λ) × Bool :=
  match M c.state c.tape.head with
  | none => (c,false)
  | some (next,op) =>
    (⟨next,match op with | .write a => c.tape.write a | .move d => c.tape.move d⟩,
      flags c.state c.tape.head)

def externalSystem (M : TM0.Machine Alphabet Λ) (flags : Λ → Alphabet → Bool)
    (initial : ExternalConfig (Λ := Λ)) : EventSystem (ExternalConfig (Λ := Λ)) :=
  ⟨initial,externalStep M flags⟩

def Rel {m : Nat} {tab : SourceTable m} {M : TM0.Machine Alphabet Λ} {flags}
    (binding : Binding M flags tab) (c : ExternalConfig (Λ := Λ)) (p : PostConfig m) : Prop :=
  c.state = binding.state p.state ∧ c.tape = p.tape

theorem step_related {m : Nat} {tab : SourceTable m} {M : TM0.Machine Alphabet Λ} {flags}
    (binding : Binding M flags tab) (c : ExternalConfig (Λ := Λ)) (p : PostConfig m)
    (h : Rel binding c p) :
    Rel binding (externalStep M flags c).1 (postStep tab p).1 ∧
      (externalStep M flags c).2 = (postStep tab p).2 := by
  obtain ⟨hs,ht⟩ := h
  cases c with
  | mk q T =>
    cases p with
    | mk p U =>
      simp only at hs ht
      subst q
      subst T
      have hr := binding.row p U.head
      have hf := binding.event p U.head
      cases ha : (selected tab p U.head).action <;>
        simp [externalStep,postStep,Rel,hr,hf,statement,ha]

/-- Every related external step is matched by one source-table step. -/
def simulation {m : Nat} {tab : SourceTable m} {M : TM0.Machine Alphabet Λ} {flags}
    (binding : Binding M flags tab) (initial : PostConfig m) :
    SegmentSimulation (externalSystem M flags ⟨binding.state initial.state,initial.tape⟩)
      (postSystem tab initial) where
  Rel := Rel binding
  initial := ⟨rfl,rfl⟩
  duration := fun _ _ => 1
  positive := by intro c p h; decide
  next := by intro c p h; exact (step_related binding c p h).1
  event_iff := by
    intro c p h
    have he := (step_related binding c p h).2
    constructor
    · intro hb
      refine ⟨0,by decide,?_⟩
      change (postStep tab p).2 = true
      rw [← he]
      exact hb
    · rintro ⟨j,hj,hb⟩
      have hj0 : j = 0 := by omega
      subst j
      change (postStep tab p).2 = true at hb
      rw [← he] at hb
      exact hb
  event_unique := by intro c p h j k hj hk hjb hkb; omega

/-- A table binding and a loaded initial tape provide the entire binary
refinement. Construction of the binding and of a blank-start loader are not
included in this theorem. -/
def binaryRefinement {m : Nat} {tab : SourceTable m} {M : TM0.Machine Alphabet Λ} {flags}
    (binding : Binding M flags tab) (start : Fin m) (initial : PostConfig m) :
    EventRefinement (externalSystem M flags ⟨binding.state initial.state,initial.tape⟩)
      (binaryFrom tab start (sourceInitial initial)) :=
  (simulation binding initial).toEventRefinement.trans
    (PostSourceRefinement.binaryRefinement tab start initial)

theorem eventuallySilent_iff {m : Nat} {tab : SourceTable m} {M : TM0.Machine Alphabet Λ} {flags}
    (binding : Binding M flags tab) (start : Fin m) (initial : PostConfig m) :
    (binaryFrom tab start (sourceInitial initial)).EventuallySilent ↔
      (externalSystem M flags ⟨binding.state initial.state,initial.tape⟩).EventuallySilent :=
  (binaryRefinement binding start initial).eventuallySilent_iff.symm

theorem infinitelyManyBeeps_iff {m : Nat} {tab : SourceTable m} {M : TM0.Machine Alphabet Λ} {flags}
    (binding : Binding M flags tab) (start : Fin m) (initial : PostConfig m) :
    (binaryFrom tab start (sourceInitial initial)).InfinitelyManyBeeps ↔
      (externalSystem M flags ⟨binding.state initial.state,initial.tape⟩).InfinitelyManyBeeps :=
  (binaryRefinement binding start initial).infinitelyManyBeeps_iff.symm

end Shared.Beeping.PostTableBinding
