import Shared.Beeping.NPcoNP.MaskInvariantRowCheck
import Shared.Beeping.NPcoNP.Parent290MaskData

/-! Kernel-checked mask-closure facts for rows 150–159 of the generated literal
program. These do not establish the producer grammar or table bindings. -/
namespace Shared.Beeping.NPcoNP.Parent290MaskShard15
open MaskInvariant Parent290MaskData
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem row150 : rowCheck program masks (150 : Fin 185) = true := by decide
theorem row151 : rowCheck program masks (151 : Fin 185) = true := by decide
theorem row152 : rowCheck program masks (152 : Fin 185) = true := by decide
theorem row153 : rowCheck program masks (153 : Fin 185) = true := by decide
theorem row154 : rowCheck program masks (154 : Fin 185) = true := by decide
theorem row155 : rowCheck program masks (155 : Fin 185) = true := by decide
theorem row156 : rowCheck program masks (156 : Fin 185) = true := by decide
theorem row157 : rowCheck program masks (157 : Fin 185) = true := by decide
theorem row158 : rowCheck program masks (158 : Fin 185) = true := by decide
theorem row159 : rowCheck program masks (159 : Fin 185) = true := by decide

end Shared.Beeping.NPcoNP.Parent290MaskShard15
