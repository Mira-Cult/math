import PASoundness.M236BreakNext
import PASoundness.M236EmitReturn
/-! The marked cleanup-style output row followed by a silent root return. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Emit
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

/-- A marked leaf entering cleanup state 68 emits one bit, then returns
silently to the root under the displayed stack and prefix conditions. -/
theorem physical_emit_cleanup_to_root (b : Bool) (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf (emitName b) 68 false .left (some b)))
    (scratch gap : Nat) (runs : List (Fin 6)) (bit : Bool) (rootTail : List Bool)
    (head : Int) (rootLeft left tail : List Bool) (c : Config 237)
    (hstack : pre.reverse ++ rootLeft = List.replicate scratch true ++ false ::
      (counterWord runs ++ List.replicate 6 false ++ false :: left))
    (hroot : counterPush runs (List.replicate (scratch + 1 + gap) false ++ true :: false :: tail) =
      true :: bit :: rootTail)
    (hrel : Related ⟨79, head,
      ⟨rootLeft, (pre ++ [last]) ++ (List.replicate gap false ++ true :: false :: tail)⟩⟩ c) :
    ∃ finish, (machineWordSystem raw rawLabels).Block c
        ((pre ++ [last]).length + ((3 * scratch + 2 * gap + 7) + (counterTime runs + 6 + 10))) finish [b] ∧
      Related ⟨79, Move.left.apply (head + (pre.length : Int)) - (scratch : Int) - 1 -
        (counterTime runs : Int) - 6 + 10,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left), rootTail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        ((pre ++ [last]).length + ((3 * scratch + 2 * gap + 7) + (counterTime runs + 6 + 10)))
        (mapConfig finish) [b] ∧
      0 < (pre ++ [last]).length ∧ 0 < (3 * scratch + 2 * gap + 7) + (counterTime runs + 6 + 10) := by
  obtain ⟨pre', last', mid, hw, hp, hr, hq, ht⟩ := physical_named_emit b (pre ++ [last]) 68 false .left
    hpath head rootLeft (List.replicate gap false ++ true :: false :: tail) c hrel
  have heq : last' :: pre'.reverse = last :: pre.reverse := by
    have hrev := congrArg List.reverse hw
    simpa [List.reverse_append] using hrev.symm
  have hlast : last' = last := (List.cons.inj heq).1
  have hpre : pre' = pre := List.reverse_inj.mp (List.cons.inj heq).2
  subst last'
  subst pre'
  have hr' : Related
      ⟨68, Move.left.apply (head + (pre.length : Int)), moveLeft
        ⟨List.replicate scratch true ++ false :: (counterWord runs ++ List.replicate 6 false ++ false :: left),
          false :: (List.replicate gap false ++ true :: false :: tail)⟩ false⟩ mid := by
    simpa [Grammar.finalTape, hstack, moveLeft] using hr
  obtain ⟨mid2, hp2, hr2, hq2, _⟩ := Break.physical_cleanup_zero_anchor scratch gap
    (Move.left.apply (head + (pre.length : Int)))
    (counterWord runs ++ List.replicate 6 false ++ false :: left) tail mid hr'
  obtain ⟨finish, hp3, hr3, hq3, _⟩ := Continue.counter_to_root runs bit rootTail
    (Move.left.apply (head + (pre.length : Int)) - (scratch : Int) - 1) left
    (List.replicate (scratch + 1 + gap) false ++ true :: false :: tail) mid2 hroot hr2
  have hphys := hp.trans (machineWordSystem raw rawLabels) (hp2.trans (machineWordSystem raw rawLabels) hp3)
  have hquot := hq.trans (machineWordSystem machine machineLabels) (hq2.trans (machineWordSystem machine machineLabels) hq3)
  exact ⟨finish, by simpa using hphys, hr3, by simpa using hquot, ht, by omega⟩
end PASoundness.M236.Emit
