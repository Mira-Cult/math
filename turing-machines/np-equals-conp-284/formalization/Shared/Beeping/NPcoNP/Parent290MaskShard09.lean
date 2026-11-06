import Shared.Beeping.NPcoNP.MaskInvariantRowCheck
import Shared.Beeping.NPcoNP.Parent290MaskData

/-! Kernel-checked mask-closure facts for rows 90–99 of the generated literal
program. These do not establish the producer grammar or table bindings. -/
namespace Shared.Beeping.NPcoNP.Parent290MaskShard09
open MaskInvariant Parent290MaskData
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem row090 : rowCheck program masks (90 : Fin 185) = true := by decide
theorem row091 : rowCheck program masks (91 : Fin 185) = true := by decide
theorem row092 : rowCheck program masks (92 : Fin 185) = true := by decide
theorem row093 : rowCheck program masks (93 : Fin 185) = true := by decide
theorem row094 : rowCheck program masks (94 : Fin 185) = true := by decide
theorem row095 : rowCheck program masks (95 : Fin 185) = true := by decide
theorem row096 : rowCheck program masks (96 : Fin 185) = true := by decide
theorem row097 : rowCheck program masks (97 : Fin 185) = true := by decide
theorem row098 : rowCheck program masks (98 : Fin 185) = true := by decide
theorem row099 : rowCheck program masks (99 : Fin 185) = true := by decide

end Shared.Beeping.NPcoNP.Parent290MaskShard09
