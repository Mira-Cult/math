import PASoundness.M236GrammarData

/-! Kernel checks for the producer-derived finite grammar graph against the
literal raw machine. The generator and metadata transcription are untrusted;
the physical row checks below use the already verified fast-table lookup. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.Grammar
open Shared.Beeping.Machines

/-- Every grammar branch has precisely its declared physical row and event. -/
theorem checked_rows : ∀ (i : Fin 158) (b : Bool), rowValid nodes i b := by decide

/-- Every nonleaf edge strictly decreases its grammar index. -/
theorem checked_decreasing : ∀ (i : Fin 158) (b : Bool), childDecreases nodes i b := by decide

theorem root_state : nodes[157].state = 79 := by decide

def allowedRuns : Nat → List Bool → Bool
  | _, [] => true
  | _, true :: tail => allowedRuns 0 tail
  | count, false :: tail => (count + 1 ≤ 5) && allowedRuns (count + 1) tail

def completePaths : List (List Bool) := paths nodes 158 157

def prefixedPaths : List (List Bool) := completePaths.map ([true, true, false] ++ ·)

theorem leaf_count : completePaths.length = 760 := by decide

theorem zero_run_bound : prefixedPaths.all (allowedRuns 0) = true := by decide

/-- The checked graph edges are rows of the actual 237-state table, including
write symbol, direction, next state and the emitted bit. -/
theorem literal_rows (i : Fin 158) (b : Bool) :
    (raw.table.row nodes[i].state b, rawLabels.at nodes[i].state b) =
      expected nodes b (edge nodes i b) := by
  have h := checked_rows i b
  simpa only [rowValid, FastTable.rows_correct, FastTable.events_correct] using h

/-- The enumeration covers every finite leaf path in the checked graph. -/
theorem every_leaf_path (word : List Bool) (h : LeafPath nodes 157 word) :
    word ∈ completePaths := by
  have hl := path_length nodes checked_decreasing h
  have hi : (157 : Fin 158).val + 1 = 158 := by decide
  rw [hi] at hl
  exact path_in_paths nodes h 158 hl

/-- No complete grammar leaf path, with its fixed root prefix, has a run of
six zeros. This quantifies over all paths in the checked finite graph. -/
theorem every_leaf_path_zero_bound (word : List Bool) (h : LeafPath nodes 157 word) :
    allowedRuns 0 ([true, true, false] ++ word) = true := by
  have hm : [true, true, false] ++ word ∈ prefixedPaths := by
    exact List.mem_map.mpr ⟨word, every_leaf_path word h, rfl⟩
  exact (List.all_eq_true.mp zero_run_bound) _ hm

/-- The enumeration neither omits nor invents any finite graph leaf path. -/
theorem leaf_path_iff_mem (word : List Bool) :
    LeafPath nodes 157 word ↔ word ∈ completePaths := by
  constructor
  · exact every_leaf_path word
  · exact paths_sound nodes 158 157 word

def nodeStates : List (Fin 237) := (List.finRange 158).map (fun i => nodes[i].state)

theorem node_states_distinct : nodeStates.Nodup := by decide

def terminalOutside (i : Fin 158) (b : Bool) : Prop :=
  match edge nodes i b with
  | .node _ => True
  | .leaf _ target .. => target ∉ nodeStates

instance (i : Fin 158) (b : Bool) : Decidable (terminalOutside i b) := by
  unfold terminalOutside
  cases edge nodes i b <;> infer_instance

/-- A declared grammar leaf really exits the grammar-state set. -/
theorem checked_terminal_outside : ∀ (i : Fin 158) (b : Bool), terminalOutside i b := by decide

end PASoundness.M236.Grammar
