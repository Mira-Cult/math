import Std

/-! Ported verbatim (apart from this provenance note and module path) from
Mira-Cult/math-wip PR 60, commit c562a134bd61560ae5efc0d2ce67680831a5b630,
`problems/pa-soundness-lean/lean/PASoundness/Refinement.lean`. Its namespace
and declarations are retained so PA consumers can migrate to this shared
module; importing both copies at once requires removing the old duplicate. -/

/-!
Ordered output refinement. The finite word on a transition is observed when
that transition exits its source configuration. This development generalizes
the scalar `Shared.Beeping` interface, retaining positive finite blocks.

No compiler or table is assumed correct by a definition here: concrete users
must construct `SegmentSimulation`, including every local block equation.
-/
namespace PASoundness

structure WordEventSystem (Config Signal : Type) where
  initial : Config
  step : Config → Config × List Signal

namespace WordEventSystem

variable {C A : Type} (M : WordEventSystem C A)

def advance (M : WordEventSystem C A) (c : C) : Nat → C
  | 0 => c
  | n + 1 => (M.step (M.advance c n)).1

def wordFrom (M : WordEventSystem C A) (c : C) : Nat → List A
  | 0 => []
  | n + 1 => M.wordFrom c n ++ (M.step (M.advance c n)).2

def run (n : Nat) : C := M.advance M.initial n
def prefixWord (n : Nat) : List A := M.wordFrom M.initial n

@[simp] theorem run_zero : M.run 0 = M.initial := rfl
@[simp] theorem run_succ (n : Nat) :
    M.run (n + 1) = (M.step (M.run n)).1 := rfl
@[simp] theorem prefix_zero : M.prefixWord 0 = [] := rfl
@[simp] theorem prefix_succ (n : Nat) :
    M.prefixWord (n + 1) = M.prefixWord n ++ (M.step (M.run n)).2 := rfl

theorem advance_add (c : C) (m n : Nat) :
    M.advance c (m + n) = M.advance (M.advance c m) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (M.step (M.advance c (m + n))).1 =
      (M.step (M.advance (M.advance c m) n)).1
    rw [ih]

theorem wordFrom_add (c : C) (m n : Nat) :
    M.wordFrom c (m + n) =
      M.wordFrom c m ++ M.wordFrom (M.advance c m) n := by
  induction n with
  | zero => simp [wordFrom]
  | succ n ih =>
    change M.wordFrom c (m + n) ++ (M.step (M.advance c (m + n))).2 =
      M.wordFrom c m ++ (M.wordFrom (M.advance c m) n ++
        (M.step (M.advance (M.advance c m) n)).2)
    rw [ih, M.advance_add, List.append_assoc]

theorem run_add (m n : Nat) :
    M.run (m + n) = M.advance (M.run m) n := M.advance_add _ _ _

theorem prefix_add (m n : Nat) :
    M.prefixWord (m + n) = M.prefixWord m ++ M.wordFrom (M.run m) n :=
  M.wordFrom_add _ _ _

/-- A finite word is an initial segment of the emitted word. Unemitted
positions are absent; no default zero is supplied. -/
def OutputPrefix (w : List A) : Prop :=
  ∃ n suffix, M.prefixWord n = w ++ suffix

/-- An indexed observation retains its position, value and multiplicity. -/
def EmitsAtPosition (k : Nat) (a : A) : Prop :=
  ∃ pre : List A, pre.length = k ∧ M.OutputPrefix (pre ++ [a])

/-- Every finite position is eventually emitted. This is a semantic property,
not an executable procedure for deciding infinite output. -/
def CompleteOutput : Prop := ∀ k, ∃ a, M.EmitsAtPosition k a

def PhysicalBits (M : WordEventSystem C Bool) : Prop :=
  ∀ n, ((M.step (M.run n)).2).length ≤ 1

theorem prefix_extends {m n : Nat} (h : m ≤ n) :
    ∃ suffix, M.prefixWord n = M.prefixWord m ++ suffix := by
  refine ⟨M.wordFrom (M.run m) (n - m), ?_⟩
  have heq : m + (n - m) = n := by omega
  rw [← heq, M.prefix_add]
  simp [heq]

def map {B : Type} (f : A → B) : WordEventSystem C B where
  initial := M.initial
  step := fun c => ((M.step c).1, (M.step c).2.map f)

@[simp] theorem map_advance {B : Type} (f : A → B) (c : C) (n : Nat) :
    (M.map f).advance c n = M.advance c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (M.step ((M.map f).advance c n)).1 = (M.step (M.advance c n)).1
    rw [ih]

@[simp] theorem map_wordFrom {B : Type} (f : A → B) (c : C) (n : Nat) :
    (M.map f).wordFrom c n = (M.wordFrom c n).map f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (M.map f).wordFrom c n ++ ((M.step ((M.map f).advance c n)).2).map f =
      (M.wordFrom c n ++ (M.step (M.advance c n)).2).map f
    rw [ih, M.map_advance, List.map_append]

@[simp] theorem map_run {B : Type} (f : A → B) (n : Nat) :
    (M.map f).run n = M.run n := M.map_advance f M.initial n

@[simp] theorem map_prefix {B : Type} (f : A → B) (n : Nat) :
    (M.map f).prefixWord n = (M.prefixWord n).map f := M.map_wordFrom f M.initial n

end WordEventSystem

/-- Equality of complete ordered output, for either finite or infinite output.
Timing and silence may differ. Order, repeats, and zero bits are preserved. -/
def SameOutput {S T A : Type} (source : WordEventSystem S A)
    (target : WordEventSystem T A) : Prop :=
  ∀ w, source.OutputPrefix w ↔ target.OutputPrefix w

theorem sameOutput_emitsAtPosition {S T A : Type}
    {source : WordEventSystem S A} {target : WordEventSystem T A}
    (h : SameOutput source target) (k : Nat) (a : A) :
    source.EmitsAtPosition k a ↔ target.EmitsAtPosition k a := by
  unfold WordEventSystem.EmitsAtPosition
  constructor
  · rintro ⟨pre, hlen, hp⟩
    exact ⟨pre, hlen, (h _).mp hp⟩
  · rintro ⟨pre, hlen, hp⟩
    exact ⟨pre, hlen, (h _).mpr hp⟩

theorem sameOutput_complete {S T A : Type}
    {source : WordEventSystem S A} {target : WordEventSystem T A}
    (h : SameOutput source target) :
    source.CompleteOutput ↔ target.CompleteOutput := by
  unfold WordEventSystem.CompleteOutput
  simp only [sameOutput_emitsAtPosition h]

/-- Global refinement certificate. `SegmentSimulation.toRefinement` derives
the ordered prefixWord field from local block equations and initialization. -/
structure WordRefinement {S T A : Type}
    (source : WordEventSystem S A) (target : WordEventSystem T A) where
  Rel : S → T → Prop
  boundary : Nat → Nat
  progress : ∀ i, boundary i < boundary (i + 1)
  related : ∀ i, Rel (source.run i) (target.run (boundary i))
  prefix_eq : ∀ i, target.prefixWord (boundary i) = source.prefixWord i

namespace WordRefinement

variable {S T A : Type} {source : WordEventSystem S A}
  {target : WordEventSystem T A} (r : WordRefinement source target)

theorem startup_silent : target.prefixWord (r.boundary 0) = [] := by
  rw [r.prefix_eq, WordEventSystem.prefix_zero]

theorem boundary_mono {i j : Nat} (h : i ≤ j) : r.boundary i ≤ r.boundary j := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step j _ ih => exact Nat.le_trans ih (Nat.le_of_lt (r.progress j))

theorem boundary_strict {i j : Nat} (h : i < j) : r.boundary i < r.boundary j := by
  exact Nat.lt_of_lt_of_le (r.progress i) (r.boundary_mono (by omega))

theorem boundary_ge (i : Nat) : r.boundary 0 + i ≤ r.boundary i := by
  induction i with
  | zero => omega
  | succ i ih => have hp := r.progress i; omega

theorem cofinal (t : Nat) : ∃ i, t < r.boundary i := by
  refine ⟨t + 1, ?_⟩
  have hg := r.boundary_ge (t + 1)
  omega

/-- No physical suffix is ignored: cofinality is used for the reverse
direction, including a target event at any arbitrarily late finite time. -/
theorem sameOutput (r : WordRefinement source target) : SameOutput source target := by
  intro w
  constructor
  · rintro ⟨n, suffix, hn⟩
    exact ⟨r.boundary n, suffix, (r.prefix_eq n).trans hn⟩
  · rintro ⟨n, suffix, hn⟩
    obtain ⟨i, hi⟩ := r.cofinal n
    obtain ⟨tail, ht⟩ := target.prefix_extends (Nat.le_of_lt hi)
    refine ⟨i, suffix ++ tail, ?_⟩
    rw [← r.prefix_eq i, ht, hn, List.append_assoc]

theorem emitsAtPosition_iff (r : WordRefinement source target) (k : Nat) (a : A) :
    source.EmitsAtPosition k a ↔ target.EmitsAtPosition k a :=
  sameOutput_emitsAtPosition r.sameOutput k a

theorem completeOutput_iff (r : WordRefinement source target) : source.CompleteOutput ↔ target.CompleteOutput :=
  sameOutput_complete r.sameOutput

def refl (M : WordEventSystem S A) : WordRefinement M M where
  Rel := Eq
  boundary := id
  progress := fun i => Nat.lt_succ_self i
  related := fun _ => rfl
  prefix_eq := fun _ => rfl

def trans {U : Type} {last : WordEventSystem U A}
    (r₂ : WordRefinement target last) : WordRefinement source last where
  Rel := fun s u => ∃ t, r.Rel s t ∧ r₂.Rel t u
  boundary := fun i => r₂.boundary (r.boundary i)
  progress := fun i => r₂.boundary_strict (r.progress i)
  related := fun i => ⟨target.run (r.boundary i), r.related i, r₂.related (r.boundary i)⟩
  prefix_eq := fun i => (r₂.prefix_eq (r.boundary i)).trans (r.prefix_eq i)

/-- Replacing each event by its fixed finite-alphabet label commutes with
refinement. This theorem does not claim that a noninjective map is reversible. -/
def map {B : Type} (f : A → B) : WordRefinement (source.map f) (target.map f) where
  Rel := r.Rel
  boundary := r.boundary
  progress := r.progress
  related := by intro i; simpa using r.related i
  prefix_eq := by intro i; simp only [WordEventSystem.map_prefix, r.prefix_eq]

end WordRefinement

/-- Compiler obligations for one source step. The duration is a natural number,
strictly positive on related configurations. The target's finite silent startup
is checked separately. No arbitrary-program termination claim is implicit. -/
structure SegmentSimulation {S T A : Type}
    (source : WordEventSystem S A) (target : WordEventSystem T A) where
  Rel : S → T → Prop
  startup : Nat
  initial : Rel source.initial (target.run startup)
  startup_silent : target.prefixWord startup = []
  duration : S → T → Nat
  positive : ∀ s t, Rel s t → 0 < duration s t
  next : ∀ s t, Rel s t →
    Rel (source.step s).1 (target.advance t (duration s t))
  word_eq : ∀ s t, Rel s t →
    target.wordFrom t (duration s t) = (source.step s).2

namespace SegmentSimulation

variable {S T A : Type} {source : WordEventSystem S A}
  {target : WordEventSystem T A} (r : SegmentSimulation source target)

def boundary : Nat → Nat
  | 0 => r.startup
  | i + 1 => boundary i + r.duration (source.run i) (target.run (boundary i))

theorem related_boundary (i : Nat) :
    r.Rel (source.run i) (target.run (r.boundary i)) := by
  induction i with
  | zero => simpa [boundary] using r.initial
  | succ i ih =>
    have hn := r.next _ _ ih
    change r.Rel (source.step (source.run i)).1
      (target.run (r.boundary i + r.duration (source.run i) (target.run (r.boundary i))))
    rw [WordEventSystem.run_add]
    exact hn

theorem boundary_progress (i : Nat) : r.boundary i < r.boundary (i + 1) := by
  have hp := r.positive _ _ (r.related_boundary i)
  change r.boundary i < r.boundary i + r.duration (source.run i) (target.run (r.boundary i))
  omega

theorem prefix_eq (i : Nat) : target.prefixWord (r.boundary i) = source.prefixWord i := by
  induction i with
  | zero => exact r.startup_silent
  | succ i ih =>
    change target.prefixWord (r.boundary i + r.duration (source.run i) (target.run (r.boundary i))) = _
    rw [WordEventSystem.prefix_add, ih, r.word_eq _ _ (r.related_boundary i)]
    rfl

def toRefinement : WordRefinement source target where
  Rel := r.Rel
  boundary := r.boundary
  progress := r.boundary_progress
  related := r.related_boundary
  prefix_eq := r.prefix_eq

theorem sameOutput (r : SegmentSimulation source target) : SameOutput source target := r.toRefinement.sameOutput

theorem completeOutput_iff (r : SegmentSimulation source target) : source.CompleteOutput ↔ target.CompleteOutput :=
  r.toRefinement.completeOutput_iff

end SegmentSimulation

/-- A universally quantified compiler fixture: two physical transitions per
source transition, one silent then one exact ordered output. -/
def delayTwo {S A : Type} (source : WordEventSystem S A) : WordEventSystem (S × Bool) A where
  initial := (source.initial, false)
  step := fun (s, phase) => if phase then (((source.step s).1, false), (source.step s).2)
    else ((s, true), [])

def delayTwoSimulation {S A : Type} (source : WordEventSystem S A) :
    SegmentSimulation source (delayTwo source) where
  Rel := fun s t => t = (s, false)
  startup := 0
  initial := rfl
  startup_silent := rfl
  duration := fun _ _ => 2
  positive := by intros; decide
  next := by
    intro s t ht
    subst t
    simp [WordEventSystem.advance, delayTwo]
  word_eq := by
    intro s t ht
    subst t
    simp [WordEventSystem.wordFrom, WordEventSystem.advance, delayTwo]

theorem delayTwo_preserves_ordered_output {S A : Type} (source : WordEventSystem S A) :
    SameOutput source (delayTwo source) := (delayTwoSimulation source).sameOutput

/-- One silent initialization transition, followed by the exact source. The
startup can be composed with positive-block refinements without discarding
any event. -/
def silentBoot {S A : Type} (source : WordEventSystem S A) : WordEventSystem (Option S) A where
  initial := none
  step := fun c => match c with
    | none => (some source.initial, [])
    | some s => (some (source.step s).1, (source.step s).2)

def silentBootSimulation {S A : Type} (source : WordEventSystem S A) :
    SegmentSimulation source (silentBoot source) where
  Rel := fun s t => t = some s
  startup := 1
  initial := rfl
  startup_silent := rfl
  duration := fun _ _ => 1
  positive := by intros; decide
  next := by
    intro s t ht
    subst t
    rfl
  word_eq := by
    intro s t ht
    subst t
    rfl

theorem silentBoot_preserves_ordered_output {S A : Type} (source : WordEventSystem S A) :
    SameOutput source (silentBoot source) := (silentBootSimulation source).sameOutput

/-- Physical legality is not a consequence of word equality. A multi-signal
abstract transition is rejected by the separate guard. -/
def simultaneousBits : WordEventSystem Unit Bool where
  initial := ()
  step := fun _ => ((), [false, true])

theorem simultaneousBits_not_physical : ¬ simultaneousBits.PhysicalBits := by
  intro h
  have hzero := h 0
  change 2 ≤ 1 at hzero
  omega

end PASoundness
