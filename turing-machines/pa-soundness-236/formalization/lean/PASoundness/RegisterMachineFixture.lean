import PASoundness.RegisterMachine
import PASoundness.MachineFixture

/-!
A five-instruction register program implemented by the complete six-state
binary machine. The proof uses exact local physical transitions, including
both decrement/test outcomes; it does not assume whole-trace equivalence.
-/
namespace PASoundness.RegisterMachineFixture
open RegisterMachine

/-- The cyclic source program emits zero, increments its sole counter, emits
one, decrements the positive counter, and takes the zero-test return branch. -/
def program : Program 1 5 where
  code := #v[
    ⟨.emit false, 1, 1⟩,
    ⟨.inc 0, 2, 2⟩,
    ⟨.emit true, 3, 3⟩,
    ⟨.decNZ 0, 4, 0⟩,
    ⟨.decNZ 0, 2, 0⟩]
  start := 0

def zeroBank : Bank 1 := fun _ => 0
def oneBank : Bank 1 := fun _ => 1

def point0 : Config 1 5 := ⟨0, zeroBank⟩
def point1 : Config 1 5 := ⟨1, zeroBank⟩
def point2 : Config 1 5 := ⟨2, oneBank⟩
def point3 : Config 1 5 := ⟨3, oneBank⟩
def point4 : Config 1 5 := ⟨4, zeroBank⟩

theorem write_zero_one : write zeroBank 0 1 = oneBank := by
  funext q
  have hq : q = 0 := Fin.eq_of_val_eq (by have h := q.isLt; omega)
  subst q
  rfl

theorem write_one_zero : write oneBank 0 0 = zeroBank := by
  funext q
  have hq : q = 0 := Fin.eq_of_val_eq (by have h := q.isLt; omega)
  subst q
  rfl

theorem step0 : program.system.step point0 = (point1, [false]) := rfl

theorem step1 : program.system.step point1 = (point2, []) := by
  change ((⟨2, write zeroBank 0 1⟩ : Config 1 5), []) = (point2, [])
  rw [write_zero_one]
  rfl

theorem step2 : program.system.step point2 = (point3, [true]) := rfl

theorem step3 : program.system.step point3 = (point4, []) := by
  change ((⟨4, write oneBank 0 0⟩ : Config 1 5), []) = (point4, [])
  rw [write_one_zero]
  rfl

theorem step4 : program.system.step point4 = (point0, []) := rfl

theorem program_cycle : program.system.Block point0 5 point0 [false, true] := by
  have h₀ := WordEventSystem.Block.single program.system step0
  have h₁ := h₀.snoc program.system step1
  have h₂ := h₁.snoc program.system step2
  have h₃ := h₂.snoc program.system step3
  simpa using h₃.snoc program.system step4

theorem program_prefix_at_cycle (count : Nat) :
    program.system.prefixWord (5*count) =
      (List.replicate count [false, true]).flatten :=
  (program_cycle.iterate program.system count).output

/-- The physical data update happens on the output row; the intermediate
phases record that pending source update explicitly. At cycle boundaries
both the counter and the physical data cell are zero. -/
def Related (s : Config 1 5) (t : Shared.Beeping.Machines.Config 6) : Prop :=
  (s = point0 ∧ t = MachineFixture.ready false) ∨
  (s = point1 ∧ t = MachineFixture.returning true) ∨
  (s = point2 ∧ t = MachineFixture.ready true) ∨
  (s = point3 ∧ t = MachineFixture.detour false) ∨
  (s = point4 ∧ t = MachineFixture.far false)

def duration (s : Config 1 5) (_ : Shared.Beeping.Machines.Config 6) : Nat :=
  if s.state = 4 then 2 else 1

theorem duration_positive (s : Config 1 5) (t : Shared.Beeping.Machines.Config 6) :
    0 < duration s t := by
  unfold duration
  split <;> decide

theorem final_return : MachineFixture.physical.Block (MachineFixture.far false) 2
    (MachineFixture.ready false) [] := by
  simpa using (WordEventSystem.Block.single MachineFixture.physical
    (MachineFixture.far_step false)).trans MachineFixture.physical
      (WordEventSystem.Block.single MachineFixture.physical (MachineFixture.return_step false))

theorem local_blocks (s : Config 1 5) (t : Shared.Beeping.Machines.Config 6)
    (h : Related s t) : ∃ finish,
      MachineFixture.physical.Block t (duration s t) finish (program.system.step s).2 ∧
        Related (program.system.step s).1 finish := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rw [step0]
    exact ⟨_, WordEventSystem.Block.single _ MachineFixture.zero_step,
      Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
  · rw [step1]
    exact ⟨_, WordEventSystem.Block.single _ (MachineFixture.return_step true),
      Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))⟩
  · rw [step2]
    exact ⟨_, WordEventSystem.Block.single _ MachineFixture.one_step,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩)))⟩
  · rw [step3]
    exact ⟨_, WordEventSystem.Block.single _ (MachineFixture.detour_step false),
      Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩)))⟩
  · rw [step4]
    exact ⟨_, final_return, Or.inl ⟨rfl,rfl⟩⟩

def simulation : SegmentSimulation program.system MachineFixture.physical :=
  SegmentSimulation.ofBlocks Related 2 (MachineFixture.ready false)
    MachineFixture.startup_block (Or.inl ⟨rfl,rfl⟩) duration
    (fun s t _ => duration_positive s t) local_blocks

/-- Closed finite-program-to-literal-table implementation. -/
def implementation : ImplementationCertificate program.system MachineFixture.machine where
  labels := MachineFixture.labels
  simulation := simulation

theorem exact_output : SameOutput program.system MachineFixture.physical :=
  implementation.sameOutput

theorem same_alternating_output : SameOutput MachineFixture.source program.system := by
  intro word
  exact (MachineFixture.exact_output word).trans (exact_output word).symm

theorem complete_output : program.system.CompleteOutput :=
  implementation.completeOutput_iff.mpr MachineFixture.complete_output

end PASoundness.RegisterMachineFixture
