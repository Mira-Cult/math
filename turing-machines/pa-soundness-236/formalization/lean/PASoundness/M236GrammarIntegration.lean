import PASoundness.M236GrammarCodec
import PASoundness.M236GrammarWalk

/-! Connect the checked grammar paths to both the literal physical segment
and the independently proved return-counter representation. This does not
establish that a selected source instruction prepares the path tape. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Grammar
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryAnchor

/-- Every root leaf path has a bounded-run counter encoding and, when its
bits are present on the full tape at raw state 79, follows its actual literal
rows in finite positive time with the exact final event. -/
theorem root_path_and_counter (word : List Bool) (h : LeafPath nodes 157 word)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head, ⟨left, word ++ tail⟩⟩ c) :
    (∃ (runs : List (Fin 6)) (bit : Bool) (pcTail : List Bool),
      counterWord runs = ([true, true, false] ++ word).reverse ∧
      counterPush runs [] = true :: bit :: pcTail) ∧
    (∃ (pre : List Bool) (j : Fin 158) (bit : Bool) (name : String)
      (target : Fin 237) (write : Bool) (move : Move) (event : Option Bool) (finish : Config 237),
      word = pre ++ [bit] ∧ edge nodes j bit = .leaf name target write move event ∧
      (machineWordSystem raw rawLabels).Block c word.length finish event.toList ∧
      Related ⟨target, move.apply (head + (pre.length : Int)),
        finalTape pre bit write move left tail⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) word.length
        (mapConfig finish) event.toList ∧ 0 < word.length) := by
  refine ⟨leaf_path_codec word h, ?_⟩
  have hroot : Related ⟨nodes[157].state, head, ⟨left, word ++ tail⟩⟩ c := by
    simpa only [root_state] using hrel
  exact physical_follow_leaf h head left tail c hroot

end PASoundness.M236.Grammar
