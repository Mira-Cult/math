import PASoundness.M236Continue
import PASoundness.M236Emit
/-! The marked output leaf followed by a silent continue return. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Emit
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

/-- A literal marked output followed by the literal return preserves the one
emitted bit. The path, complete-tape factorization and root prefix are explicit. -/
theorem physical_emit_to_root (b : Bool) (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf (emitName b) 72 true .left (some b)))
    (first : Nat) (runs : List (Fin 6)) (bit : Bool) (rootTail : List Bool)
    (head : Int) (rootLeft left tail : List Bool) (c : Config 237)
    (hstack : pre.reverse ++ rootLeft = List.replicate first false ++ true ::
      (counterWord runs ++ List.replicate 6 false ++ false :: left))
    (hroot : counterPush runs (List.replicate first false ++ true :: tail) = true :: bit :: rootTail)
    (hrel : Related ⟨79, head, ⟨rootLeft, (pre ++ [last]) ++ tail⟩⟩ c) :
    ∃ finish, (machineWordSystem raw rawLabels).Block c
        ((pre ++ [last]).length + (first + 1 + (counterTime runs + 6 + 10))) finish [b] ∧
      Related ⟨79, Move.left.apply (head + (pre.length : Int)) - (first : Int) - 1 -
        (counterTime runs : Int) - 6 + 10,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left), rootTail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        ((pre ++ [last]).length + (first + 1 + (counterTime runs + 6 + 10))) (mapConfig finish) [b] ∧
      0 < (pre ++ [last]).length ∧ 0 < first + 1 + (counterTime runs + 6 + 10) := by
  obtain ⟨pre', last', mid, hw, hp, hr, hq, ht⟩ :=
    physical_named_emit b (pre ++ [last]) 72 true .left hpath head rootLeft tail c hrel
  have heq : last' :: pre'.reverse = last :: pre.reverse := by
    have hrev := congrArg List.reverse hw
    simpa [List.reverse_append] using hrev.symm
  have hlast : last' = last := (List.cons.inj heq).1
  have hpre : pre' = pre := List.reverse_inj.mp (List.cons.inj heq).2
  subst last'
  subst pre'
  have hr' : Related
      ⟨72, Move.left.apply (head + (pre.length : Int)),
        moveLeft ⟨List.replicate first false ++ true ::
          (counterWord runs ++ List.replicate 6 false ++ false :: left), true :: tail⟩ true⟩ mid := by
    simpa [Grammar.finalTape, hstack, moveLeft] using hr
  obtain ⟨finish, hp', hr'', hq', ht'⟩ := Continue.physical_one_to_root first runs bit rootTail
    (Move.left.apply (head + (pre.length : Int))) left tail true mid hroot hr'
  exact ⟨finish, by simpa using hp.trans (machineWordSystem raw rawLabels) hp', hr'',
    by simpa using hq.trans (machineWordSystem machine machineLabels) hq', ht, ht'⟩
end PASoundness.M236.Emit
