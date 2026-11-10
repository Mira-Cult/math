import PASoundness.M236Grammar
import PASoundness.M236UnaryShift

/-! Every path in the checked finite control graph is a literal physical
segment, provided the input bits are present on the tape. The last edge's
actual optional event is retained. This is a local path theorem, not a proof
that a source instruction reaches the prepared tape. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Grammar
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift

def finalTape (pre : List Bool) (bit write : Bool) (move : Move)
    (left tail : List Bool) : Tape :=
  match move with
  | .left => moveLeft ⟨pre.reverse ++ left, bit :: tail⟩ write
  | .right => moveRight ⟨pre.reverse ++ left, bit :: tail⟩ write

/-- A graph leaf path is realized by the literal table from a zipper containing
its input bits. The complete final tape and the exact final-row event remain
in the conclusion. -/
theorem follow_leaf_path {i : Fin 158} {word : List Bool} (h : LeafPath nodes i word)
    (head : Int) (left tail : List Bool) :
    ∃ (pre : List Bool) (j : Fin 158) (bit : Bool) (name : String)
      (target : Fin 237) (write : Bool) (move : Move) (event : Option Bool),
      word = pre ++ [bit] ∧ edge nodes j bit = .leaf name target write move event ∧
      rawSystem.Block ⟨nodes[i].state, head, ⟨left, word ++ tail⟩⟩ word.length
        ⟨target, move.apply (head + (pre.length : Int)), finalTape pre bit write move left tail⟩
        event.toList := by
  induction h generalizing head left with
  | leaf i bit name target write move event he =>
    have hr := literal_rows i bit
    rw [he] at hr
    have hrow : raw.table.row nodes[i].state bit = ⟨write, move, target, false⟩ := by
      simpa [expected] using congrArg Prod.fst hr
    have hev : rawLabels.at nodes[i].state bit = event := by
      simpa [expected] using congrArg Prod.snd hr
    have hs : rawSystem.step ⟨nodes[i].state, head, ⟨left, bit :: tail⟩⟩ =
        (⟨target, move.apply head, finalTape [] bit write move left tail⟩, event.toList) := by
      cases move <;> simp only [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read,
        List.headD_cons, hrow, hev, finalTape, List.reverse_nil, List.nil_append]
    refine ⟨[], i, bit, name, target, write, move, event, rfl, he, ?_⟩
    simpa using WordEventSystem.Block.single rawSystem hs
  | step i j bit path he rest ih =>
    have hr := literal_rows i bit
    rw [he] at hr
    have hrow : raw.table.row nodes[i].state bit = ⟨bit, .right, nodes[j].state, false⟩ := by
      simpa [expected] using congrArg Prod.fst hr
    have hev : rawLabels.at nodes[i].state bit = none := by
      simpa [expected] using congrArg Prod.snd hr
    have hs : rawSystem.step ⟨nodes[i].state, head, ⟨left, bit :: (path ++ tail)⟩⟩ =
        (⟨nodes[j].state, head + 1, ⟨bit :: left, path ++ tail⟩⟩, []) := by
      simp only [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, List.headD_cons,
        hrow, hev, Move.apply, moveRight, Option.toList_none, List.drop_succ_cons, List.drop_zero]
    obtain ⟨pre, k, last, name, target, write, move, event, hp, hl, hb⟩ := ih (head + 1) (bit :: left)
    have hwhole := (WordEventSystem.Block.single rawSystem hs).trans rawSystem hb
    refine ⟨bit :: pre, k, last, name, target, write, move, event, ?_, hl, ?_⟩
    · simp [hp]
    · have hh : head + 1 + (pre.length : Int) = head + ((bit :: pre).length : Int) := by
        simp only [List.length_cons]; omega
      simpa only [List.cons_append, List.length_cons, Nat.succ_eq_add_one, List.nil_append,
        hh, finalTape, List.reverse_cons, List.append_assoc, List.singleton_append, Nat.add_comm] using hwhole

/-- The path block transfers to the full raw and selected quotient tapes,
with the same duration and ordered event list. -/
theorem physical_follow_leaf {i : Fin 158} {word : List Bool} (h : LeafPath nodes i word)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨nodes[i].state, head, ⟨left, word ++ tail⟩⟩ c) :
    ∃ (pre : List Bool) (j : Fin 158) (bit : Bool) (name : String)
      (target : Fin 237) (write : Bool) (move : Move) (event : Option Bool) (finish : Config 237),
      word = pre ++ [bit] ∧ edge nodes j bit = .leaf name target write move event ∧
      (machineWordSystem raw rawLabels).Block c word.length finish event.toList ∧
      Related ⟨target, move.apply (head + (pre.length : Int)),
        finalTape pre bit write move left tail⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) word.length
        (mapConfig finish) event.toList ∧ 0 < word.length := by
  obtain ⟨pre, j, bit, name, target, write, move, event, hw, he, hb⟩ :=
    follow_leaf_path h head left tail
  have hs := advance_sound raw rawLabels hrel word.length
  change Related (rawSystem.advance ⟨nodes[i].state, head, ⟨left, word ++ tail⟩⟩ word.length) _ ∧
    rawSystem.wordFrom ⟨nodes[i].state, head, ⟨left, word ++ tail⟩⟩ word.length = _ at hs
  rw [hb.endpoint, hb.output] at hs
  let finish := (machineWordSystem raw rawLabels).advance c word.length
  have hp : (machineWordSystem raw rawLabels).Block c word.length finish event.toList := ⟨rfl, hs.2.symm⟩
  refine ⟨pre, j, bit, name, target, write, move, event, finish, hw, he, hp, hs.1,
    BootstrapScan.mapped_block hp, ?_⟩
  rw [hw]
  simp

end PASoundness.M236.Grammar
