import Shared.Beeping.NPcoNP.MaskInvariantRowCheck
import Shared.Beeping.NPcoNP.Parent290MaskData

/-! Kernel-checked mask-closure facts for rows 80–89 of the generated literal
program. These do not establish the producer grammar or table bindings. -/
namespace Shared.Beeping.NPcoNP.Parent290MaskShard08
open MaskInvariant Parent290MaskData
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem row080 : rowCheck program masks (80 : Fin 185) = true := by decide
theorem row081 : rowCheck program masks (81 : Fin 185) = true := by decide
theorem row082 : rowCheck program masks (82 : Fin 185) = true := by decide
theorem row083 : rowCheck program masks (83 : Fin 185) = true := by decide
theorem row084 : rowCheck program masks (84 : Fin 185) = true := by decide
theorem row085 : rowCheck program masks (85 : Fin 185) = true := by decide
theorem row086 : rowCheck program masks (86 : Fin 185) = true := by decide
theorem row087 : rowCheck program masks (87 : Fin 185) = true := by decide
theorem row088 : rowCheck program masks (88 : Fin 185) = true := by decide
theorem row089 : rowCheck program masks (89 : Fin 185) = true := by decide

end Shared.Beeping.NPcoNP.Parent290MaskShard08
