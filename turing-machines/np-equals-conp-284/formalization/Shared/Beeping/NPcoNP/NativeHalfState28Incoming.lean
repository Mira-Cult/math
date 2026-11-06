import Shared.Beeping.NPcoNP.Table284

/-! A finite check of the rows entering physical state 28. -/
namespace Shared.Beeping.NPcoNP.NativeHalfState28Incoming

open Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284

set_option maxRecDepth 32768
set_option maxHeartbeats 20000000

theorem enters28_write_left_zero (q : Fin 284) (b : Bool)
    (h : (machine.table.row q b).next = 28) :
    (machine.table.row q b).write = false ∧
      (machine.table.row q b).move = .right := by
  have hcheck : ∀ (q : Fin 284) (b : Bool),
      (machine.table.row q b).next = 28 →
        (machine.table.row q b).write = false ∧
          (machine.table.row q b).move = .right := by decide
  exact hcheck q b h

end Shared.Beeping.NPcoNP.NativeHalfState28Incoming
