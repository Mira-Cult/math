import PASoundness.Refinement
import Shared.Beeping.Machines

/-!
Ordered binary observations on the pinned ordinary machine hardware.
The copied `Shared.Beeping` definitions retain their original scalar flag;
the new finite label vector observes the same configurations and does not
inspect proofs, formulas, or arbitrary tape predicates.
-/
namespace PASoundness

open Shared.Beeping Shared.Beeping.Machines

/-- Exactly two static optional-bit labels per physical state. `none` is
silence; a present bit is emitted on exit through that row. -/
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

/-- The label map cannot alter the ordinary machine's execution. -/
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

/-- Physical singleton legality is proved separately from flattened-word
equality. Arbitrary abstract transition words need not satisfy this guard. -/
theorem machineWordSystem_physicalBits {n : Nat} (M : Machine n) (labels : BitLabels n) :
    (machineWordSystem M labels).PhysicalBits := by
  intro t
  rw [machineWordSystem_event]
  cases labels.at (M.system.run t).state ((M.system.run t).tape (M.system.run t).head) <;>
    simp

theorem machineWordSystem_finite_support {n : Nat} (M : Machine n)
    (labels : BitLabels n) (t : Nat) :
    ∃ touched : List Int, ∀ pos, pos ∉ touched →
      ((machineWordSystem M labels).run t).tape pos = M.blank := by
  rw [machineWordSystem_run]
  exact M.run_finite_support t

/-- A reusable conditional certificate. No instance for PA926 is declared:
its source/compiler/loader/row correspondence remains a separate obligation. -/
structure ImplementationCertificate {S : Type} (source : WordEventSystem S Bool)
    {n : Nat} (M : Machine n) where
  labels : BitLabels n
  simulation : SegmentSimulation source (machineWordSystem M labels)

namespace ImplementationCertificate

variable {S : Type} {source : WordEventSystem S Bool} {n : Nat} {M : Machine n}

theorem sameOutput (cert : ImplementationCertificate source M) :
    SameOutput source (machineWordSystem M cert.labels) := cert.simulation.sameOutput

theorem completeOutput_iff (cert : ImplementationCertificate source M) :
    source.CompleteOutput ↔ (machineWordSystem M cert.labels).CompleteOutput :=
  cert.simulation.completeOutput_iff

theorem emitsAtPosition_iff (cert : ImplementationCertificate source M) (k : Nat) (b : Bool) :
    source.EmitsAtPosition k b ↔ (machineWordSystem M cert.labels).EmitsAtPosition k b :=
  cert.simulation.toRefinement.emitsAtPosition_iff k b

theorem physicalBits (cert : ImplementationCertificate source M) :
    (machineWordSystem M cert.labels).PhysicalBits := machineWordSystem_physicalBits _ _

end ImplementationCertificate

namespace MachineFixtures

/-- Complete literal one-state table. Every transition writes blank and moves
right; the static event map is what distinguishes the following controls. -/
def drift : Machine 1 where
  table := ⟨#v[(⟨false, .right, 0, false⟩, ⟨false, .right, 0, false⟩)]⟩
  start := 0
  blank := false
  startHead := 0

def zeros : BitLabels 1 := BitLabels.ofFn fun _ _ => some false
def ones : BitLabels 1 := BitLabels.ofFn fun _ _ => some true
def silent : BitLabels 1 := BitLabels.ofFn fun _ _ => none

theorem zeros_emit_first_zero :
    (machineWordSystem drift zeros).EmitsAtPosition 0 false := by
  refine ⟨[], rfl, 1, [], ?_⟩
  rfl

theorem silent_prefix (t : Nat) : (machineWordSystem drift silent).prefixWord t = [] := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [WordEventSystem.prefix_succ, ih]
    simp [machineWordSystem, silent, BitLabels.at_ofFn]

theorem silent_has_no_position (k : Nat) (b : Bool) :
    ¬ (machineWordSystem drift silent).EmitsAtPosition k b := by
  rintro ⟨pre, _, t, suffix, h⟩
  rw [silent_prefix] at h
  have hlen := congrArg List.length h
  simp at hlen

/-- Identical configurations with a dropped-event map do not implement the
same ordered output. Finite timing invariance does not permit bit deletion. -/
theorem dropped_event_map_rejected :
    ¬ SameOutput (machineWordSystem drift zeros) (machineWordSystem drift silent) := by
  intro h
  exact silent_has_no_position 0 false ((sameOutput_emitsAtPosition h 0 false).mp
    zeros_emit_first_zero)

theorem ones_prefix_excludes_zero (t : Nat) :
    false ∉ (machineWordSystem drift ones).prefixWord t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [WordEventSystem.prefix_succ]
    simp only [List.mem_append, not_or]
    constructor
    · exact ih
    · simp [machineWordSystem, ones]

theorem ones_never_emit_zero (k : Nat) :
    ¬ (machineWordSystem drift ones).EmitsAtPosition k false := by
  rintro ⟨pre, _, t, suffix, h⟩
  have hz : false ∈ (machineWordSystem drift ones).prefixWord t := by
    rw [h]
    simp
  exact ones_prefix_excludes_zero t hz

/-- A changed BIT0/BIT1 map is not a timing change. The underlying hardware
run is identical, yet the ordered stream differs at position zero. -/
theorem flipped_event_map_rejected :
    ¬ SameOutput (machineWordSystem drift zeros) (machineWordSystem drift ones) := by
  intro h
  exact ones_never_emit_zero 0 ((sameOutput_emitsAtPosition h 0 false).mp
    zeros_emit_first_zero)

end MachineFixtures
end PASoundness
