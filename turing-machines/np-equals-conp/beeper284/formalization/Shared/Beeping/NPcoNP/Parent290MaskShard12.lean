import Shared.Beeping.NPcoNP.MaskInvariantRowCheck
import Shared.Beeping.NPcoNP.Parent290MaskData

/-! Kernel-checked mask-closure facts for rows 120–129 of the generated literal
program. These do not establish the producer grammar or table bindings. -/
namespace Shared.Beeping.NPcoNP.Parent290MaskShard12
open MaskInvariant Parent290MaskData
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem row120 : rowCheck program masks (120 : Fin 185) = true := by decide
theorem row121 : rowCheck program masks (121 : Fin 185) = true := by decide
theorem row122 : rowCheck program masks (122 : Fin 185) = true := by decide
theorem row123 : rowCheck program masks (123 : Fin 185) = true := by decide
theorem row124 : rowCheck program masks (124 : Fin 185) = true := by decide
theorem row125 : rowCheck program masks (125 : Fin 185) = true := by decide
theorem row126 : rowCheck program masks (126 : Fin 185) = true := by decide
theorem row127 : rowCheck program masks (127 : Fin 185) = true := by decide
theorem row128 : rowCheck program masks (128 : Fin 185) = true := by decide
theorem row129 : rowCheck program masks (129 : Fin 185) = true := by decide

end Shared.Beeping.NPcoNP.Parent290MaskShard12
