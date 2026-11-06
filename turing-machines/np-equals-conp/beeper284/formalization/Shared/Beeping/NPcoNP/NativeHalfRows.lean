import Shared.Beeping.NPcoNP.Table284

/-! The literal transition rows for the native-HALF cycle's suffix scanner
and shift. These finite identities do not establish a tape representation,
termination, or the correctness of any multi-step physical segment. -/

namespace Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem row32_zero : machine.table.row 32 false = ⟨false, .right, 33, false⟩ := by decide
theorem row32_one : machine.table.row 32 true = ⟨true, .right, 32, false⟩ := by decide
theorem row33_zero : machine.table.row 33 false = ⟨false, .left, 34, false⟩ := by decide
theorem row33_one : machine.table.row 33 true = ⟨true, .right, 32, false⟩ := by decide
theorem row34_zero : machine.table.row 34 false = ⟨true, .left, 35, false⟩ := by decide
theorem row34_one : machine.table.row 34 true = ⟨true, .left, 34, false⟩ := by decide
theorem row35_zero : machine.table.row 35 false = ⟨false, .left, 31, false⟩ := by decide
theorem row35_one : machine.table.row 35 true = ⟨false, .left, 34, false⟩ := by decide

end Shared.Beeping.NPcoNP.NativeHalfRows
