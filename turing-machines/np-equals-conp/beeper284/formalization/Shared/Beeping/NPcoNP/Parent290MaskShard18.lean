import Shared.Beeping.NPcoNP.MaskInvariantRowCheck
import Shared.Beeping.NPcoNP.Parent290MaskData

/-! Kernel-checked mask-closure facts for rows 180–184 of the generated literal
program. These do not establish the producer grammar or table bindings. -/
namespace Shared.Beeping.NPcoNP.Parent290MaskShard18
open MaskInvariant Parent290MaskData
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem row180 : rowCheck program masks (180 : Fin 185) = true := by decide
theorem row181 : rowCheck program masks (181 : Fin 185) = true := by decide
theorem row182 : rowCheck program masks (182 : Fin 185) = true := by decide
theorem row183 : rowCheck program masks (183 : Fin 185) = true := by decide
theorem row184 : rowCheck program masks (184 : Fin 185) = true := by decide

end Shared.Beeping.NPcoNP.Parent290MaskShard18
