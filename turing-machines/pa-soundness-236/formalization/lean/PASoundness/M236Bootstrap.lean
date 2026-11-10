import PASoundness.M236Quotient

/-!
The actual five-state bootstrap subgraph and its unique exit, on arbitrary
two-way tapes. These are safety properties; termination and the advertised
runtime-entry geometry are separate obligations.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Bootstrap

open Shared.Beeping Shared.Beeping.Machines

def rawState (q : Fin 237) : Prop := q = 0 ∨ q = 75 ∨ q = 76 ∨ q = 77 ∨ q = 78
def selectedState (q : Fin 236) : Prop := q = 0 ∨ q = 74 ∨ q = 75 ∨ q = 76 ∨ q = 77

instance (q : Fin 237) : Decidable (rawState q) := by unfold rawState; infer_instance
instance (q : Fin 236) : Decidable (selectedState q) := by unfold selectedState; infer_instance

/-- Every bootstrap row is silent; only the read-one row of state 76 can
leave the five-state raw subgraph. -/
theorem raw_rows (q : Fin 237) (b : Bool) (h : rawState q) :
    rawLabels.at q b = none ∧
      (rawState (raw.table.row q b).next ∨
        (q = 76 ∧ b = true ∧ (raw.table.row q b).next = 58)) := by
  rcases h with h | h | h | h | h <;> subst q <;> cases b <;> decide

theorem selected_rows (q : Fin 236) (b : Bool) (h : selectedState q) :
    machineLabels.at q b = none ∧
      (selectedState (machine.table.row q b).next ∨
        (q = 75 ∧ b = true ∧ (machine.table.row q b).next = 57)) := by
  rcases h with h | h | h | h | h <;> subst q <;> cases b <;> decide

theorem mapped_state (q : Fin 237) : rawState q ↔ selectedState (mapState q) := by
  decide +revert

/-- The first non-bootstrap transition leaves on the unique marked row. -/
theorem raw_exit (c : Config 237) (hb : rawState c.state)
    (he : ¬ rawState (raw.step c).1.state) :
    c.state = 76 ∧ c.tape c.head = true ∧ (raw.step c).1.state = 58 ∧
      (raw.step c).1.head = c.head + 1 ∧ (raw.step c).1.tape = c.tape ∧
      rawLabels.at c.state (c.tape c.head) = none := by
  have hr := raw_rows c.state (c.tape c.head) hb
  have hn : ¬ rawState (raw.table.row c.state (c.tape c.head)).next := by
    simpa [Machine.step] using he
  have hx := hr.2.resolve_left hn
  rcases hx with ⟨hq, hb, ht⟩
  have row : raw.table.row 76 true = ⟨true, .right, 58, false⟩ := by decide
  refine ⟨hq, hb, ?_, ?_, ?_, hr.1⟩
  · simpa [Machine.step] using ht
  · simp [Machine.step, hq, hb, row, Move.apply]
  · funext x
    simp only [Machine.step, hq, hb, row]
    change (if x = c.head then true else c.tape x) = c.tape x
    by_cases hx : x = c.head
    · simpa [hx] using hb.symm
    · simp [hx]

theorem selected_exit (c : Config 236) (hb : selectedState c.state)
    (he : ¬ selectedState (machine.step c).1.state) :
    c.state = 75 ∧ c.tape c.head = true ∧ (machine.step c).1.state = 57 ∧
      (machine.step c).1.head = c.head + 1 ∧ (machine.step c).1.tape = c.tape ∧
      machineLabels.at c.state (c.tape c.head) = none := by
  have hr := selected_rows c.state (c.tape c.head) hb
  have hn : ¬ selectedState (machine.table.row c.state (c.tape c.head)).next := by
    simpa [Machine.step] using he
  have hx := hr.2.resolve_left hn
  rcases hx with ⟨hq, hb, ht⟩
  have row : machine.table.row 75 true = ⟨true, .right, 57, false⟩ := by decide
  refine ⟨hq, hb, ?_, ?_, ?_, hr.1⟩
  · simpa [Machine.step] using ht
  · simp [Machine.step, hq, hb, row, Move.apply]
  · funext x
    simp only [Machine.step, hq, hb, row]
    change (if x = c.head then true else c.tape x) = c.tape x
    by_cases hx : x = c.head
    · simpa [hx] using hb.symm
    · simp [hx]

/-- No output can precede the first transition out of the bootstrap states,
regardless of how long that finite prefix lasts. -/
theorem raw_prefix_silent (t : Nat)
    (h : ∀ i, i < t → rawState (raw.system.run i).state) :
    (machineWordSystem raw rawLabels).prefixWord t = [] := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [WordEventSystem.prefix_succ, ih (fun i hi => h i (by omega))]
    rw [machineWordSystem_event]
    have hs := (raw_rows (raw.system.run t).state
      ((raw.system.run t).tape (raw.system.run t).head) (h t (by omega))).1
    simp [hs]

theorem selected_prefix_silent (t : Nat)
    (h : ∀ i, i < t → selectedState (machine.system.run i).state) :
    (machineWordSystem machine machineLabels).prefixWord t = [] := by
  rw [← prefix_eq t]
  apply raw_prefix_silent
  intro i hi
  apply (mapped_state _).mpr
  simpa [← map_run i, mapConfig] using h i hi

end PASoundness.M236.Bootstrap
