import PASoundness.M236UnaryAnchor

/-! The literal prepared state-9 tape has an anchor, nine zero-valued
registers, a finite control path and a blank suffix. The checked 68-step
endpoint contains the restored anchor, first register incremented to one,
the other eight zeros, and no events. This is not a blank-start proof. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
open PASoundness Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236 PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift
example : rawSystem.Block
    ⟨9, 0, ⟨[false, true, false, false, false, true, true] ++ List.replicate 7 false,
      [true, false, true, false, true, false, true, false, true, false,
       true, false, true, false, true, false, true, false, false]⟩⟩ 68
    ⟨79, -4, ⟨[false, true, true] ++ List.replicate 7 false,
      [false, false, true, false, true, true, false, true, false, true, false,
       true, false, true, false, true, false, true, false, true, false, true, false]⟩⟩ [] := by
  constructor <;> decide

example : PASoundness.M236.UnaryAnchor.counterPush ([0, 0] : List (Fin 6)) [] = [true, true] := by decide
example : PASoundness.M236.UnaryAnchor.counterPush ([0] : List (Fin 6)) [] ≠ [true, true] := by decide
