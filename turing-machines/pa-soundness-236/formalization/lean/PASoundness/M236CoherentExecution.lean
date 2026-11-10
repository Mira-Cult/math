import PASoundness.M236OccurrenceGraphProjection
/-! A single coherent, non-stalling sequence of physical graph segments. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236
open PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

structure Advancement (a : Snapshot) where
  after : Snapshot
  duration : Nat
  events : List Bool
  valid : GraphStep a after duration events

noncomputable def advance (a : Snapshot) (ha : Good a) : Advancement a :=
  Classical.choice (show Nonempty (Advancement a) from by
    obtain ⟨b, duration, events, hstep, _⟩ := good_step a ha
    exact ⟨⟨b, duration, events, hstep⟩⟩)

/-- These choices form one coherent sequence, not separate prefixes. -/
noncomputable def states : (n : Nat) → {s : Snapshot // Good s}
  | 0 => ⟨initial, initial_good⟩
  | n + 1 =>
    let p := states n
    let step := advance p.val p.property
    ⟨step.after, step.valid.2.1⟩

noncomputable def segment (n : Nat) : Advancement (states n).val :=
  advance (states n).val (states n).property

noncomputable def elapsed : Nat → Nat
  | 0 => 0
  | n + 1 => elapsed n + (segment n).duration

noncomputable def output : Nat → List Bool
  | 0 => []
  | n + 1 => output n ++ (segment n).events

theorem next_state (n : Nat) : (states (n+1)).val = (segment n).after := rfl

theorem segment_positive (n : Nat) : 0 < (segment n).duration := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hpositive, _⟩ := (segment n).valid
  exact hpositive

theorem elapsed_strict : StrictMono elapsed := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [elapsed]
  have := segment_positive n
  omega

theorem elapsed_lower (n : Nat) : n ≤ elapsed n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [elapsed]
    have := segment_positive n
    omega

theorem coherent_raw (n : Nat) :
    (states n).val.config = (machineWordSystem raw rawLabels).run (89821408 + elapsed n) ∧
    (machineWordSystem raw rawLabels).prefixWord (89821408 + elapsed n) = output n := by
  induction n with
  | zero =>
    exact ⟨rfl, raw_initial_canonical_budget.2.2⟩
  | succ n ih =>
    have hs := (segment n).valid
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hblock⟩ := hs
    constructor
    · rw [elapsed, ← Nat.add_assoc, WordEventSystem.run_add, ← ih.1, next_state]
      exact hblock.endpoint.symm
    · rw [elapsed, output, ← Nat.add_assoc, WordEventSystem.prefix_add, ih.2, ← ih.1]
      exact congrArg (output n ++ ·) hblock.output

/-- Every prefix of the same sequence projects to the independent graph relation. -/
theorem coherent_witness_walk (n : Nat) :
    WitnessWalk graphInitial n (output n) (states n).val.graphState := by
  induction n with
  | zero =>
    simpa [states, output, initial_graph_state] using (WitnessWalk.nil (start := graphInitial))
  | succ n ih =>
    have h := graph_step_projects _ _ _ _ (segment n).valid
    simpa only [output, next_state] using WitnessWalk.snoc ih h

/-- One sequence of strictly increasing physical times realizes every graph
segment on the literal selected 236-state blank-start execution. -/
theorem selected_coherent_execution :
    StrictMono elapsed ∧ (∀ n, n ≤ elapsed n) ∧
    ∀ n, Good (states n).val ∧
      GraphStep (states n).val (states (n+1)).val (segment n).duration (segment n).events ∧
      mapConfig (states n).val.config = (machineWordSystem machine machineLabels).run (89821408 + elapsed n) ∧
      (machineWordSystem machine machineLabels).prefixWord (89821408 + elapsed n) = output n := by
  refine ⟨elapsed_strict, elapsed_lower, ?_⟩
  intro n
  refine ⟨(states n).property, ?_, ?_, ?_⟩
  · rw [next_state]
    exact (segment n).valid
  · rw [(coherent_raw n).1, machineWordSystem_run, map_run, ← machineWordSystem_run machine machineLabels]
  · rw [← prefix_eq, (coherent_raw n).2]
end PASoundness.M236.OccurrenceGraph
