import PASoundness.M236MetadataFormat
import PASoundness.M236Grammar

/-! The generated metadata orderings and leaf labels are checked against the
finite grammar; the separate metadata text theorem binds their serializations
to the retained file. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.Metadata
open PASoundness.M236.Grammar

theorem grammar_order_complete : grammarOrder.Perm (List.finRange 158) := by decide

theorem state_order_complete : stateOrder.Perm (List.finRange 237) := by decide

def resolvedLeaf (name : String) (bit : Bool) : String :=
  if name == "_continue.1" then "6.continue.0"
  else if name == "_continue.2" then "6.continue.1"
  else if name == "_continue.3" then "6.continue.2"
  else if name == "_break.1" then "6.break.1"
  else if name == "_break.3" then "6.break.3"
  else if name == "emit.0" || name == "emit.1" then
    if bit then "6.break.0" else "6.continue.0"
  else name

def leafEvent (name : String) : Option Bool :=
  if name == "emit.0" then some false else if name == "emit.1" then some true else none

def leafNamed (i : Fin 158) (b : Bool) : Prop :=
  match edge nodes i b with
  | .node _ => True
  | .leaf name target _ _ event =>
      stateNames[target] = resolvedLeaf name b ∧ event = leafEvent name

instance (i : Fin 158) (b : Bool) : Decidable (leafNamed i b) := by
  unfold leafNamed
  cases edge nodes i b <;> infer_instance

/-- Every leaf label names its declared state and emitted bit according to
the metadata's state map and the control-return naming convention. -/
theorem leaf_names_checked : ∀ (i : Fin 158) (b : Bool), leafNamed i b := by decide

end PASoundness.M236.Metadata
