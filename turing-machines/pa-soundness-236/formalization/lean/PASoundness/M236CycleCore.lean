import PASoundness.M236Redispatch
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Redispatch
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

/-- Every named increment edge in the finite checked grammar preserves its
input bit. This finite check ranges over all nodes, bits, and registers. -/
theorem increment_edge_write : ∀ (i : Fin 158) (bit : Bool) (r : Fin 9) (write : Bool),
    Grammar.edge Grammar.nodes i bit =
      .leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none →
    write = bit := by decide

/-- A named increment path preserves its final path bit at the leaf. -/
theorem named_increment_ending (r : Fin 9) (write : Bool) {i : Fin 158}
    {word : List Bool} {e : Grammar.Edge} (h : Preparation.NamedPath Grammar.nodes i word e)
    (heq : e = .leaf ("3." ++ Selector.registerNames[r] ++ ".inc")
      (Selector.entryState r) write .right none) :
    ∃ pre bit, word = pre ++ [bit] ∧ write = bit := by
  induction h with
  | leaf i b e he hl =>
    rw [heq] at he
    exact ⟨[], b, rfl, increment_edge_write i b r write he⟩
  | step i j b tail e he rest ih =>
    obtain ⟨pre, bit, hw, hbit⟩ := ih heq
    exact ⟨b :: pre, bit, by simp [hw], hbit⟩
end PASoundness.M236.Redispatch
