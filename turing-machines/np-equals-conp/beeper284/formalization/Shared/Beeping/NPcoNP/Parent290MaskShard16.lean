import Shared.Beeping.NPcoNP.MaskInvariantRowCheck
import Shared.Beeping.NPcoNP.Parent290MaskData

/-! Kernel-checked mask-closure facts for rows 160–169 of the generated literal
program. These do not establish the producer grammar or table bindings. -/
namespace Shared.Beeping.NPcoNP.Parent290MaskShard16
open MaskInvariant Parent290MaskData
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem row160 : rowCheck program masks (160 : Fin 185) = true := by decide
theorem row161 : rowCheck program masks (161 : Fin 185) = true := by decide
theorem row162 : rowCheck program masks (162 : Fin 185) = true := by decide
theorem row163 : rowCheck program masks (163 : Fin 185) = true := by decide
theorem row164 : rowCheck program masks (164 : Fin 185) = true := by decide
theorem row165 : rowCheck program masks (165 : Fin 185) = true := by decide
theorem row166 : rowCheck program masks (166 : Fin 185) = true := by decide
theorem row167 : rowCheck program masks (167 : Fin 185) = true := by decide
theorem row168 : rowCheck program masks (168 : Fin 185) = true := by decide
theorem row169 : rowCheck program masks (169 : Fin 185) = true := by decide

end Shared.Beeping.NPcoNP.Parent290MaskShard16
