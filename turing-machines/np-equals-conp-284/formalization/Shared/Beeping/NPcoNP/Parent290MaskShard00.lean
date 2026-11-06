import Shared.Beeping.NPcoNP.MaskInvariantRowCheck
import Shared.Beeping.NPcoNP.Parent290MaskData

/-! Kernel-checked mask-closure facts for rows 0–9 of the generated literal
program. These do not establish the producer grammar or table bindings. -/
namespace Shared.Beeping.NPcoNP.Parent290MaskShard00
open MaskInvariant Parent290MaskData
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem row000 : rowCheck program masks (0 : Fin 185) = true := by decide
theorem row001 : rowCheck program masks (1 : Fin 185) = true := by decide
theorem row002 : rowCheck program masks (2 : Fin 185) = true := by decide
theorem row003 : rowCheck program masks (3 : Fin 185) = true := by decide
theorem row004 : rowCheck program masks (4 : Fin 185) = true := by decide
theorem row005 : rowCheck program masks (5 : Fin 185) = true := by decide
theorem row006 : rowCheck program masks (6 : Fin 185) = true := by decide
theorem row007 : rowCheck program masks (7 : Fin 185) = true := by decide
theorem row008 : rowCheck program masks (8 : Fin 185) = true := by decide
theorem row009 : rowCheck program masks (9 : Fin 185) = true := by decide

end Shared.Beeping.NPcoNP.Parent290MaskShard00
