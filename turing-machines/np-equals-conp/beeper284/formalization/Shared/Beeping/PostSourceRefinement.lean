import Shared.Beeping.BinarySourceLoaded

/-! Connect the finite source table to mathlib's two-way post-Turing tape.
The caller supplies the initial post-Turing tape. The subsequent refinement
to a loaded binary tape is proved; a blank-start loader is not supplied. -/
namespace Shared.Beeping.PostSourceRefinement
open Turing
open Shared.Beeping.ComparisonAlphabetBits Shared.Beeping.ComparisonSingleTape
open Shared.Beeping.BinarySourceCompiler Shared.Beeping.BinarySourceRefinement
open Shared.Beeping.BinarySourceLoaded

structure PostConfig (m : Nat) where
  state : Fin m
  tape : Tape Alphabet

def postStep {m : Nat} (tab : SourceTable m) (c : PostConfig m) : PostConfig m × Bool :=
  let r := selected tab c.state c.tape.head
  (match r.action with
   | .write a => ⟨r.next,c.tape.write a⟩
   | .left => ⟨r.next,c.tape.move Dir.left⟩
   | .right => ⟨r.next,c.tape.move Dir.right⟩,r.beep)

/-- The same literal source table as a total mathlib post-Turing machine.
The event bit remains a separate fixed row flag. -/
def tm0 {m : Nat} (tab : SourceTable m) (start : Fin m) :
    letI : Inhabited (Fin m) := ⟨start⟩
    TM0.Machine Alphabet (Fin m) :=
  letI : Inhabited (Fin m) := ⟨start⟩
  fun q a =>
    let r := selected tab q a
    some (r.next, match r.action with
      | .write b => .write b
      | .left => .move .left
      | .right => .move .right)

/-- The configuration change is exactly mathlib `TM0.step`; no separate tape
or direction convention is assumed. -/
theorem postStep_tm0 {m : Nat} (tab : SourceTable m) (start : Fin m) (c : PostConfig m) :
    letI : Inhabited (Fin m) := ⟨start⟩
    TM0.step (tm0 tab start) ⟨c.state,c.tape⟩ =
      some ⟨(postStep tab c).1.state,(postStep tab c).1.tape⟩ := by
  letI : Inhabited (Fin m) := ⟨start⟩
  cases h : (selected tab c.state c.tape.head).action <;> simp [TM0.step,tm0,postStep,h]

def postSystem {m : Nat} (tab : SourceTable m) (initial : PostConfig m) : EventSystem (PostConfig m) :=
  ⟨initial,postStep tab⟩

def sourceInitial {m : Nat} (initial : PostConfig m) : SourceConfig m :=
  ⟨initial.state,0,initial.tape.nth⟩

def Rel {m : Nat} (p : PostConfig m) (c : SourceConfig m) : Prop :=
  c.state = p.state ∧ ∀ i, c.tape (c.head+i) = p.tape.nth i

theorem initial_related {m : Nat} (initial : PostConfig m) : Rel initial (sourceInitial initial) := by
  simp [Rel,sourceInitial]

/-- One source-table transition agrees with the corresponding post-Turing
write or move, including its event. -/
theorem step_related {m : Nat} (tab : SourceTable m) (p : PostConfig m) (c : SourceConfig m)
    (h : Rel p c) :
    Rel (postStep tab p).1 (sourceStep tab c).1 ∧ (sourceStep tab c).2 = (postStep tab p).2 := by
  obtain ⟨hs,ht⟩ := h
  have hh : c.tape c.head = p.tape.head := by
    have h0 := ht 0
    simpa using h0
  have hr : selected tab c.state (c.tape c.head) = selected tab p.state p.tape.head := by rw [hs,hh]
  cases ha : (selected tab p.state p.tape.head).action with
  | write a =>
    simp only [postStep,sourceStep,hr,ha,Prod.fst,Prod.snd]
    constructor
    · constructor
      · trivial
      · intro i
        rw [Tape.write_nth]
        by_cases hi : i = 0
        · subst i
          simp [Function.update]
        · have hn : c.head+i ≠ c.head := by omega
          simp [Function.update_of_ne hn,hi,ht i]
    · trivial
  | left =>
    simp only [postStep,sourceStep,hr,ha,Prod.fst,Prod.snd]
    constructor
    · constructor
      · trivial
      · intro i
        rw [Tape.move_left_nth]
        have he : c.head-1+i = c.head+(i-1) := by omega
        rw [he]
        exact ht (i-1)
    · trivial
  | right =>
    simp only [postStep,sourceStep,hr,ha,Prod.fst,Prod.snd]
    constructor
    · constructor
      · trivial
      · intro i
        rw [Tape.move_right_nth]
        have he : c.head+1+i = c.head+(i+1) := by omega
        rw [he]
        exact ht (i+1)
    · trivial

/-- The two finite-alphabet tape presentations match one-for-one, with no
stuttering and identical event words. -/
def simulation {m : Nat} (tab : SourceTable m) (initial : PostConfig m) :
    SegmentSimulation (postSystem tab initial) (sourceFrom tab (sourceInitial initial)) where
  Rel := Rel
  initial := initial_related initial
  duration := fun _ _ => 1
  positive := by intro p c h; decide
  next := by
    intro p c h
    exact (step_related tab p c h).1
  event_iff := by
    intro p c h
    have he := (step_related tab p c h).2
    constructor
    · intro hb
      refine ⟨0,by decide,?_⟩
      change (sourceStep tab c).2 = true
      rw [he]
      exact hb
    · rintro ⟨j,hj,hb⟩
      have hj0 : j = 0 := by omega
      subst j
      change (sourceStep tab c).2 = true at hb
      rw [he] at hb
      exact hb
  event_unique := by
    intro p c h j k hj hk hjb hkb
    omega

/-- Composition gives a progress-sensitive refinement from a loaded
post-Turing tape to the actual binary transition table. -/
def binaryRefinement {m : Nat} (tab : SourceTable m) (start : Fin m) (initial : PostConfig m) :
    EventRefinement (postSystem tab initial) (binaryFrom tab start (sourceInitial initial)) :=
  (simulation tab initial).toEventRefinement.trans
    (BinarySourceLoaded.simulation tab start (sourceInitial initial)).toEventRefinement

theorem eventuallySilent_iff {m : Nat} (tab : SourceTable m) (start : Fin m) (initial : PostConfig m) :
    (binaryFrom tab start (sourceInitial initial)).EventuallySilent ↔ (postSystem tab initial).EventuallySilent :=
  (binaryRefinement tab start initial).eventuallySilent_iff.symm

theorem infinitelyManyBeeps_iff {m : Nat} (tab : SourceTable m) (start : Fin m) (initial : PostConfig m) :
    (binaryFrom tab start (sourceInitial initial)).InfinitelyManyBeeps ↔ (postSystem tab initial).InfinitelyManyBeeps :=
  (binaryRefinement tab start initial).infinitelyManyBeeps_iff.symm

end Shared.Beeping.PostSourceRefinement
