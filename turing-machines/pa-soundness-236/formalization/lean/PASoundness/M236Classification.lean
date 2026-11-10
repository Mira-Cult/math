import PASoundness.M236TransferInvariant
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

def supportedLeaf (last : Bool) (e : Grammar.Edge) : Prop :=
  (∃ (r : Fin 9) (write : Bool), e = .leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none) ∨
  (∃ (r : Fin 9) (write : Bool), e = .leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none) ∨
  e = .leaf "_continue.1" 72 false .left none ∨
  e = .leaf "_continue.2" 73 false .left none ∨
  e = .leaf "_continue.3" 74 false .left none ∨
  e = .leaf "_break.1" 69 false .left none ∨
  e = .leaf "_break.3" 71 false .left none ∨
  (∃ b : Bool, last = false ∧ e = .leaf (Emit.emitName b) 72 true .left (some b)) ∨
  (∃ b : Bool, last = true ∧ e = .leaf (Emit.emitName b) 68 false .left (some b))

instance (last : Bool) (e : Grammar.Edge) : Decidable (supportedLeaf last e) := by
  unfold supportedLeaf
  infer_instance

def supportedEdge (last : Bool) (e : Grammar.Edge) : Prop :=
  match e with
  | .node _ => True
  | .leaf .. => supportedLeaf last e

instance (last : Bool) (e : Grammar.Edge) : Decidable (supportedEdge last e) := by
  unfold supportedEdge
  cases e <;> infer_instance

theorem all_edges_supported : ∀ (i : Fin 158) (last : Bool),
    supportedEdge last (Grammar.edge Grammar.nodes i last) := by decide

theorem leaf_named_supported {i : Fin 158} {word : List Bool}
    (h : Grammar.LeafPath Grammar.nodes i word) :
    ∃ last e, word.getLast? = some last ∧ Preparation.NamedPath Grammar.nodes i word e ∧ supportedLeaf last e := by
  induction h with
  | leaf i b name target write move event he =>
    have hs := all_edges_supported i b
    rw [he] at hs
    exact ⟨b, _, by simp, .leaf i b _ he ⟨_, _, _, _, _, rfl⟩, hs⟩
  | step i j b tail he rest ih =>
    obtain ⟨last, e, hl, hn, hs⟩ := ih
    refine ⟨last, e, ?_, .step i j b tail e he hn, hs⟩
    cases tail with
    | nil => simp at hl
    | cons c xs => simpa using hl
end PASoundness.M236.Control
