import Shared.Beeping.WordRefinement
import Shared.Beeping.Refinement
import Shared.Beeping.Machines

/-!
Ordered finite transition words are the pinned PR 60 observer interface.
The physical bit-label definitions below preserve its `PASoundness` names and
are transcribed from commit c562a134bd61560ae5efc0d2ce67680831a5b630,
`problems/pa-soundness-lean/lean/PASoundness/Machine.lean`. A future merge must
replace duplicate upstream declarations by imports of this shared module.
Scalar erasure discards bit values deliberately; it does not preserve an
observer that distinguishes zero and one.
-/
namespace PASoundness
open Shared.Beeping Shared.Beeping.Machines

/-- Static optional-bit labels for the two rows of each physical state. -/
abbrev BitLabels (n : Nat) := Vector (Option Bool × Option Bool) n

def BitLabels.at {n : Nat} (labels : BitLabels n) (q : Fin n) (read : Bool) : Option Bool :=
  if read then labels[q].2 else labels[q].1

def BitLabels.ofFn {n : Nat} (f : Fin n → Bool → Option Bool) : BitLabels n :=
  Vector.ofFn fun q => (f q false, f q true)

@[simp] theorem BitLabels.at_ofFn {n : Nat} (f : Fin n → Bool → Option Bool)
    (q : Fin n) (read : Bool) : (BitLabels.ofFn f).at q read = f q read := by
  cases read <;> simp [BitLabels.ofFn, BitLabels.at]

def machineWordSystem {n : Nat} (M : Machine n) (labels : BitLabels n) :
    WordEventSystem (Config n) Bool where
  initial := M.initial
  step := fun c => ((M.step c).1, (labels.at c.state (c.tape c.head)).toList)

theorem machineWordSystem_run {n : Nat} (M : Machine n) (labels : BitLabels n) (t : Nat) :
    (machineWordSystem M labels).run t = M.system.run t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [WordEventSystem.run_succ, EventSystem.run_succ, ih]
    rfl

theorem machineWordSystem_event {n : Nat} (M : Machine n) (labels : BitLabels n) (t : Nat) :
    ((machineWordSystem M labels).step ((machineWordSystem M labels).run t)).2 =
      (labels.at (M.system.run t).state
        ((M.system.run t).tape (M.system.run t).head)).toList := by
  rw [machineWordSystem_run]
  rfl

theorem machineWordSystem_physicalBits {n : Nat} (M : Machine n) (labels : BitLabels n) :
    (machineWordSystem M labels).PhysicalBits := by
  intro t
  rw [machineWordSystem_event]
  cases labels.at (M.system.run t).state ((M.system.run t).tape (M.system.run t).head) <;> simp

theorem eventSystem_ext {C : Type} {M N : EventSystem C}
    (hi : M.initial = N.initial) (hs : M.step = N.step) : M = N := by
  cases M
  cases N
  simp_all

namespace WordEventSystem

/-- Forget the values and multiplicity within a transition word, retaining
whether that transition emitted at least one symbol. -/
def erase {C A : Type} (W : WordEventSystem C A) : EventSystem C where
  initial := W.initial
  step := fun c => ((W.step c).1, !(W.step c).2.isEmpty)

@[simp] theorem erase_run {C A : Type} (W : WordEventSystem C A) (t : Nat) :
    W.erase.run t = W.run t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [EventSystem.run_succ, WordEventSystem.run_succ, ih]
    rfl

theorem erase_beep_iff {C A : Type} (W : WordEventSystem C A) (t : Nat) :
    W.erase.BeepAt t ↔ (W.step (W.run t)).2 ≠ [] := by
  change (Bool.not ((W.step (W.erase.run t)).2.isEmpty) = true) ↔ _
  rw [erase_run]
  simp

/-- Embed a scalar beeper as a word stream with one unit signal per beep. -/
def ofBeep {C : Type} (M : EventSystem C) : WordEventSystem C Unit where
  initial := M.initial
  step := fun c => ((M.step c).1, if (M.step c).2 then [()] else [])

@[simp] theorem erase_ofBeep {C : Type} (M : EventSystem C) : (ofBeep M).erase = M := by
  apply eventSystem_ext
  · rfl
  · funext c
    change ((M.step c).1, !((if (M.step c).2 then [()] else []) : List Unit).isEmpty) = M.step c
    cases h : M.step c with
    | mk d b => cases b <;> simp

/-- Every observer defined from the complete ordered-prefix relation is
invariant under exact ordered-output refinement. The observer may use any
finite or countable logical quantifiers over that relation. -/
theorem observer_preserved {S T A : Type} {source : WordEventSystem S A}
    {target : WordEventSystem T A} (h : SameOutput source target)
    (observer : (List A → Prop) → Prop) :
    observer source.OutputPrefix ↔ observer target.OutputPrefix := by
  have he : source.OutputPrefix = target.OutputPrefix := by
    funext w
    exact propext (h w)
  rw [he]

end WordEventSystem

/-- Preserve every original beep as a singleton `true` output. This adapter
is useful for comparing scalar controllers with ordered-output systems. -/
def BitLabels.fromFlags {n : Nat} (M : Machine n) : BitLabels n :=
  BitLabels.ofFn fun q b => if (M.table.row q b).beep then some true else none

theorem fromFlags_erase {n : Nat} (M : Machine n) :
    (machineWordSystem M (BitLabels.fromFlags M)).erase = M.system := by
  apply eventSystem_ext
  · rfl
  · funext c
    simp only [WordEventSystem.erase,machineWordSystem,BitLabels.fromFlags,BitLabels.at_ofFn,
      Machine.system,Machine.step]
    cases h : (M.table.row c.state (c.tape c.head)).beep <;> simp

/-- For arbitrary row labels, erasure agrees with the original scalar event
exactly when every row's flag equals label presence. -/
def FlagsMatch {n : Nat} (M : Machine n) (labels : BitLabels n) : Prop :=
  ∀ q b, (labels.at q b).isSome = (M.table.row q b).beep

theorem erase_machine_of_match {n : Nat} (M : Machine n) (labels : BitLabels n)
    (h : FlagsMatch M labels) : (machineWordSystem M labels).erase = M.system := by
  apply eventSystem_ext
  · rfl
  · funext c
    have hh := h c.state (c.tape c.head)
    simp only [WordEventSystem.erase,machineWordSystem,Machine.system,Machine.step]
    cases hv : labels.at c.state (c.tape c.head) <;> simp_all

/-- The row-presence condition is also necessary for equality of the total
step functions, including rows that a particular initial run never visits. -/
theorem erase_machine_iff_match {n : Nat} (M : Machine n) (labels : BitLabels n) :
    (machineWordSystem M labels).erase = M.system ↔ FlagsMatch M labels := by
  constructor
  · intro he q b
    have hs := congrArg (fun E : EventSystem (Config n) =>
      (E.step ⟨q,0,fun _ => b⟩).2) he
    change Bool.not ((labels.at q b).toList.isEmpty) = (M.table.row q b).beep at hs
    cases hv : labels.at q b <;> simp_all
  · exact erase_machine_of_match M labels

/-- The PR 60 positive-block certificate preserves every such observer. -/
theorem SegmentSimulation.observer_preserved {S T A : Type}
    {source : WordEventSystem S A} {target : WordEventSystem T A}
    (r : SegmentSimulation source target) (observer : (List A → Prop) → Prop) :
    observer source.OutputPrefix ↔ observer target.OutputPrefix :=
  WordEventSystem.observer_preserved r.sameOutput observer

end PASoundness
