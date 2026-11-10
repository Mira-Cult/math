import PASoundness.Machine
import PASoundness.LocalSimulation

/-!
A complete six-state binary single-tape implementation fixture. It initializes
a marker silently, toggles a data cell, and follows a longer branch after one
than after zero. Its infinite ordered output is proved from local row blocks.
It is deliberately independent of the PA926 compiler or table binding.
-/
namespace PASoundness.MachineFixture

open Shared.Beeping Shared.Beeping.Machines

/-- Six states and both binary rows in every state. State two branches on the
stored data bit. Its zero branch returns in two steps; its one branch takes a
four-step detour through cells one and two. All moves are ordinary L/R moves. -/
def machine : Machine 6 where
  table := ⟨#v[
    (⟨false, .right, 1, false⟩, ⟨false, .right, 1, false⟩),
    (⟨true, .left, 2, false⟩, ⟨true, .left, 2, false⟩),
    (⟨true, .right, 3, false⟩, ⟨false, .right, 4, false⟩),
    (⟨false, .left, 2, false⟩, ⟨true, .left, 2, false⟩),
    (⟨false, .right, 5, false⟩, ⟨true, .right, 5, false⟩),
    (⟨false, .left, 3, false⟩, ⟨true, .left, 3, false⟩)]⟩
  start := 0
  blank := false
  startHead := 0

/-- Only the two static rows leaving state two emit; the observed bit is that
row's input symbol. Every other row is silent. -/
def labels : BitLabels 6 := BitLabels.ofFn fun q read => if q = 2 then some read else none

def physical : WordEventSystem (Config 6) Bool := machineWordSystem machine labels

/-- Explicit executable source: output the current Boolean and toggle it. -/
def source : WordEventSystem Bool Bool where
  initial := false
  step := fun b => (!b, [b])

/-- Cell zero is the mutable data; cell one is the initialized marker. All
other tape cells are blank, including the detour cell two. -/
def tape (b : Bool) (position : Int) : Bool :=
  if position = 0 then b else decide (position = 1)

def ready (b : Bool) : Config 6 := ⟨2, 0, tape b⟩
def returning (b : Bool) : Config 6 := ⟨3, 1, tape b⟩
def detour (b : Bool) : Config 6 := ⟨4, 1, tape b⟩
def far (b : Bool) : Config 6 := ⟨5, 2, tape b⟩
def bootMiddle : Config 6 := ⟨1, 1, fun _ => false⟩

theorem write_data (q : Fin 6) (old new : Bool) :
    (⟨q, 0, tape old⟩ : Config 6).write new = tape new := by
  funext position
  by_cases h : position = 0 <;> simp [Config.write, tape, h]

theorem write_current {n : Nat} (c : Config n) : c.write (c.tape c.head) = c.tape := by
  funext position
  by_cases h : position = c.head <;> simp [Config.write, h]

theorem first_step : physical.step physical.initial = (bootMiddle, []) := by
  change ((⟨1, 1, machine.initial.write false⟩ : Config 6), []) = (bootMiddle, [])
  have hw : machine.initial.write false = (fun _ => false) := write_current machine.initial
  rw [hw]
  rfl

theorem initialize_marker : physical.step bootMiddle = (ready false, []) := by
  change ((⟨2, 0, bootMiddle.write true⟩ : Config 6), []) = (ready false, [])
  have hw : bootMiddle.write true = tape false := by
    funext position
    by_cases h0 : position = 0 <;> by_cases h1 : position = 1 <;>
      simp_all [bootMiddle, Config.write, tape]
  rw [hw]
  rfl

theorem zero_step : physical.step (ready false) = (returning true, [false]) := by
  change ((⟨3, 1, (ready false).write true⟩ : Config 6), [false]) = (returning true, [false])
  have hw : (ready false).write true = tape true := write_data 2 false true
  rw [hw]
  rfl

theorem one_step : physical.step (ready true) = (detour false, [true]) := by
  change ((⟨4, 1, (ready true).write false⟩ : Config 6), [true]) = (detour false, [true])
  have hw : (ready true).write false = tape false := write_data 2 true false
  rw [hw]
  rfl

theorem return_step (b : Bool) : physical.step (returning b) = (ready b, []) := by
  change ((⟨2, 0, (returning b).write true⟩ : Config 6), []) = (ready b, [])
  have hw : (returning b).write true = tape b := write_current (returning b)
  rw [hw]
  rfl

theorem detour_step (b : Bool) : physical.step (detour b) = (far b, []) := by
  change ((⟨5, 2, (detour b).write true⟩ : Config 6), []) = (far b, [])
  have hw : (detour b).write true = tape b := write_current (detour b)
  rw [hw]
  rfl

theorem far_step (b : Bool) : physical.step (far b) = (returning b, []) := by
  change ((⟨3, 1, (far b).write false⟩ : Config 6), []) = (returning b, [])
  have hw : (far b).write false = tape b := write_current (far b)
  rw [hw]
  rfl

theorem startup_block : physical.Block physical.initial 2 (ready false) [] := by
  simpa using (WordEventSystem.Block.single physical first_step).trans physical
    (WordEventSystem.Block.single physical initialize_marker)

theorem zero_block : physical.Block (ready false) 2 (ready true) [false] := by
  simpa using (WordEventSystem.Block.single physical zero_step).trans physical
    (WordEventSystem.Block.single physical (return_step true))

theorem one_block : physical.Block (ready true) 4 (ready false) [true] := by
  have h₁ := WordEventSystem.Block.single physical one_step
  have h₂ := h₁.snoc physical (detour_step false)
  have h₃ := h₂.snoc physical (far_step false)
  simpa using h₃.snoc physical (return_step false)

theorem cycle_block : physical.Block (ready false) 6 (ready false) [false, true] := by
  simpa using zero_block.trans physical one_block

/-- An explicit physical-time checkpoint formula obtained by finite block
composition, independently of the generic stream-equivalence theorem. -/
theorem repeated_cycle (count : Nat) :
    physical.Block physical.initial (2+6*count) (ready false)
      (List.replicate count [false, true]).flatten := by
  simpa using startup_block.trans physical (cycle_block.iterate physical count)

theorem physical_prefix_at_cycle (count : Nat) :
    physical.prefixWord (2+6*count) = (List.replicate count [false, true]).flatten :=
  (repeated_cycle count).output

def duration (b : Bool) (_ : Config 6) : Nat := if b then 4 else 2

theorem duration_positive (b : Bool) (c : Config 6) : 0 < duration b c := by
  cases b <;> simp [duration]

/-- This local certificate is assembled from the seven literal row proofs.
Its relation records the entire tape, state, and head at each checkpoint. -/
def simulation : SegmentSimulation source physical :=
  SegmentSimulation.ofBlocks (fun b c => c = ready b) 2 (ready false)
    startup_block rfl duration (fun b c _ => duration_positive b c)
    (by
      intro b c hc
      subst c
      cases b with
      | false => exact ⟨ready true, zero_block, rfl⟩
      | true => exact ⟨ready false, one_block, rfl⟩)

/-- A closed implementation certificate for a concrete complete binary table,
with no whole-trace correspondence supplied as an assumption. -/
def implementation : ImplementationCertificate source machine where
  labels := labels
  simulation := simulation

theorem initialized_from_blank : physical.run 2 = ready false := startup_block.endpoint

theorem startup_silent : physical.prefixWord 2 = [] := startup_block.output

theorem checkpoints (i : Nat) :
    physical.run (simulation.boundary i) = ready (source.run i) :=
  simulation.related_boundary i

theorem checkpoints_cofinal (time : Nat) : ∃ i, time < simulation.boundary i :=
  simulation.toRefinement.cofinal time

theorem exact_output : SameOutput source physical := implementation.sameOutput

theorem source_prefix_length (n : Nat) : (source.prefixWord n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [WordEventSystem.prefix_succ]
    change (source.prefixWord n ++ [source.run n]).length = n+1
    simp only [List.length_append, List.length_singleton, ih]

theorem source_emits (k : Nat) : source.EmitsAtPosition k (source.run k) := by
  refine ⟨source.prefixWord k, source_prefix_length k, k+1, [], ?_⟩
  rw [WordEventSystem.prefix_succ]
  simp only [List.append_nil]
  rfl

theorem source_complete : source.CompleteOutput :=
  fun k => ⟨source.run k, source_emits k⟩

theorem complete_output : physical.CompleteOutput :=
  implementation.completeOutput_iff.mp source_complete

theorem physical_emits (k : Nat) : physical.EmitsAtPosition k (source.run k) :=
  (implementation.emitsAtPosition_iff k (source.run k)).mp (source_emits k)

/-- Exact indexed output, including exclusion of the wrong bit at each
position. Timing differences do not change the output's positional meaning. -/
theorem physical_position_iff (k : Nat) (b : Bool) :
    physical.EmitsAtPosition k b ↔ b = source.run k := by
  constructor
  · intro h
    exact physical.emitsAtPosition_unique h (physical_emits k)
  · rintro rfl
    exact physical_emits k

theorem source_run_even (k : Nat) : source.run (2*k) = false := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : 2*(k+1) = (2*k+1)+1 := by omega
    rw [h, WordEventSystem.run_succ, WordEventSystem.run_succ, ih]
    rfl

theorem source_run_odd (k : Nat) : source.run (2*k+1) = true := by
  rw [WordEventSystem.run_succ, source_run_even]
  rfl

theorem physical_even (k : Nat) : physical.EmitsAtPosition (2*k) false := by
  rw [physical_position_iff, source_run_even]

theorem physical_odd (k : Nat) : physical.EmitsAtPosition (2*k+1) true := by
  rw [physical_position_iff, source_run_odd]

theorem ready_output (b : Bool) : (physical.step (ready b)).2 = [b] := by
  cases b
  · exact congrArg Prod.snd zero_step
  · exact congrArg Prod.snd one_step

/-- Infinitely many actual physical output transitions, beyond every finite
time bound. This is derived from local progress and literal event rows. -/
theorem outputs_after_every_time (time : Nat) :
    ∃ later, time < later ∧ ∃ b, (physical.step (physical.run later)).2 = [b] := by
  obtain ⟨i, hi⟩ := checkpoints_cofinal time
  exact ⟨simulation.boundary i, hi, source.run i, by rw [checkpoints, ready_output]⟩

end PASoundness.MachineFixture
