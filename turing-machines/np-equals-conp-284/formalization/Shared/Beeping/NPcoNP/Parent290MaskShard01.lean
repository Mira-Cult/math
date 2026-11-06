import Shared.Beeping.NPcoNP.MaskInvariantRowCheck
import Shared.Beeping.NPcoNP.Parent290MaskData

/-! Kernel-checked mask-closure facts for rows 10–19 of the generated literal
program. These do not establish the producer grammar or table bindings. -/
namespace Shared.Beeping.NPcoNP.Parent290MaskShard01
open MaskInvariant Parent290MaskData
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem row010 : rowCheck program masks (10 : Fin 185) = true := by decide
theorem row011 : rowCheck program masks (11 : Fin 185) = true := by decide
theorem row012 : rowCheck program masks (12 : Fin 185) = true := by decide
theorem row013 : rowCheck program masks (13 : Fin 185) = true := by decide
theorem row014 : rowCheck program masks (14 : Fin 185) = true := by decide
theorem row015 : rowCheck program masks (15 : Fin 185) = true := by decide
theorem row016 : rowCheck program masks (16 : Fin 185) = true := by decide
theorem row017 : rowCheck program masks (17 : Fin 185) = true := by decide
theorem row018 : rowCheck program masks (18 : Fin 185) = true := by decide
theorem row019 : rowCheck program masks (19 : Fin 185) = true := by decide

end Shared.Beeping.NPcoNP.Parent290MaskShard01
