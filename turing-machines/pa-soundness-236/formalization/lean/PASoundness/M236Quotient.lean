import PASoundness.M236Data

/-! Finite quotient checking and its consequences for the actual runs.
No source/compiler simulation is assumed or asserted here. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236
open Shared.Beeping Shared.Beeping.Machines

def mapState (q : Fin 237) : Fin 236 := quotientMap[q]

def RowsAgree (q : Fin 237) (b : Bool) : Prop :=
  let a := raw.table.row q b
  let z := machine.table.row (mapState q) b
  a.write = z.write ∧ a.move = z.move ∧ mapState a.next = z.next ∧
    rawLabels.at q b = machineLabels.at (mapState q) b

instance (q : Fin 237) (b : Bool) : Decidable (RowsAgree q b) := by
  unfold RowsAgree
  infer_instance

theorem quotient_rows : ∀ (q : Fin 237) (b : Bool), RowsAgree q b := by
  decide

theorem quotient_initial : mapState raw.start = machine.start := by decide

theorem selected_blank_start : machine.initial.state = 0 ∧ machine.initial.head = 0 ∧
    ∀ x, machine.initial.tape x = false := by
  simp [Machine.initial, machine]

theorem selected_first_transition :
    (machine.step machine.initial).1.state = 74 ∧
    (machine.step machine.initial).1.head = 1 ∧
    ((machineWordSystem machine machineLabels).step machine.initial).2 = [] := by
  decide

/-- The quotient keeps the whole tape and head and only renames the state. -/
def mapConfig (c : Config 237) : Config 236 :=
  ⟨mapState c.state, c.head, c.tape⟩

theorem map_step (c : Config 237) :
    mapConfig (raw.step c).1 = (machine.step (mapConfig c)).1 := by
  obtain ⟨hw, hm, hn, _⟩ := quotient_rows c.state (c.tape c.head)
  simp only [mapConfig, Machine.step, Config.write]
  rw [← hw, ← hm, ← hn]
  rfl

theorem map_initial : mapConfig raw.initial = machine.initial := by
  simp [mapConfig, Machine.initial, raw, machine, mapState, quotientMap]

theorem map_run (t : Nat) : mapConfig (raw.system.run t) = machine.system.run t := by
  induction t with
  | zero => exact map_initial
  | succ t ih =>
    rw [EventSystem.run_succ, EventSystem.run_succ, ← ih]
    exact map_step _

theorem event_at (t : Nat) :
    ((machineWordSystem raw rawLabels).step ((machineWordSystem raw rawLabels).run t)).2 =
    ((machineWordSystem machine machineLabels).step ((machineWordSystem machine machineLabels).run t)).2 := by
  rw [machineWordSystem_event, machineWordSystem_event, ← map_run t]
  obtain ⟨_, _, _, he⟩ := quotient_rows (raw.system.run t).state
    ((raw.system.run t).tape (raw.system.run t).head)
  simpa [mapConfig] using congrArg Option.toList he

theorem prefix_eq (t : Nat) :
    (machineWordSystem raw rawLabels).prefixWord t =
      (machineWordSystem machine machineLabels).prefixWord t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [WordEventSystem.prefix_succ, WordEventSystem.prefix_succ, ih, event_at]

/-- The full ordered output agrees, including finite or infinite streams. -/
theorem same_output : SameOutput (machineWordSystem raw rawLabels)
    (machineWordSystem machine machineLabels) := by
  intro w
  constructor <;> rintro ⟨t, suffix, h⟩ <;> refine ⟨t, suffix, ?_⟩
  · rw [← prefix_eq t]; exact h
  · rw [prefix_eq t]; exact h

/-- The four actual event rows and a silent neighboring row. -/
theorem selected_event_fixtures :
    machineLabels.at 134 false = some true ∧
    machineLabels.at 136 false = some true ∧
    machineLabels.at 137 true = some false ∧
    machineLabels.at 146 false = some false ∧
    machineLabels.at 134 true = none := by decide

theorem false_is_not_silence : machineLabels.at 137 true ≠ none := by decide

theorem true_is_not_false : machineLabels.at 134 false ≠ some false := by decide

end PASoundness.M236
