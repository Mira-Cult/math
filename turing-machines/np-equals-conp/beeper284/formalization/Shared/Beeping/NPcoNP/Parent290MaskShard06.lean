import Shared.Beeping.NPcoNP.MaskInvariantRowCheck
import Shared.Beeping.NPcoNP.Parent290MaskData

/-! Kernel-checked mask-closure facts for rows 60–69 of the generated literal
program. These do not establish the producer grammar or table bindings. -/
namespace Shared.Beeping.NPcoNP.Parent290MaskShard06
open MaskInvariant Parent290MaskData
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem row060 : rowCheck program masks (60 : Fin 185) = true := by decide
theorem row061 : rowCheck program masks (61 : Fin 185) = true := by decide
theorem row062 : rowCheck program masks (62 : Fin 185) = true := by decide
theorem row063 : rowCheck program masks (63 : Fin 185) = true := by decide
theorem row064 : rowCheck program masks (64 : Fin 185) = true := by decide
theorem row065 : rowCheck program masks (65 : Fin 185) = true := by decide
theorem row066 : rowCheck program masks (66 : Fin 185) = true := by decide
theorem row067 : rowCheck program masks (67 : Fin 185) = true := by decide
theorem row068 : rowCheck program masks (68 : Fin 185) = true := by decide
theorem row069 : rowCheck program masks (69 : Fin 185) = true := by decide

end Shared.Beeping.NPcoNP.Parent290MaskShard06
