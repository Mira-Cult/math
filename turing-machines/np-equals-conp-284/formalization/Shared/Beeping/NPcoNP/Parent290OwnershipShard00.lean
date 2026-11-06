import Shared.Beeping.NPcoNP.CoalescingMaskCheck
import Shared.Beeping.NPcoNP.Coalescing284Map
import Shared.Beeping.NPcoNP.Parent290MaskData

/-! Kernel ownership checks for generated program rows 0–9.
External source and physical bindings remain unproved. -/
namespace Shared.Beeping.NPcoNP.Parent290OwnershipShard00
open CoalescingAlgebra Coalescing284Map Parent290MaskData
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem row000 : maskAccessCheck logicalToSuffix (masks 0) program.code[0].action = true := by decide
theorem row001 : maskAccessCheck logicalToSuffix (masks 1) program.code[1].action = true := by decide
theorem row002 : maskAccessCheck logicalToSuffix (masks 2) program.code[2].action = true := by decide
theorem row003 : maskAccessCheck logicalToSuffix (masks 3) program.code[3].action = true := by decide
theorem row004 : maskAccessCheck logicalToSuffix (masks 4) program.code[4].action = true := by decide
theorem row005 : maskAccessCheck logicalToSuffix (masks 5) program.code[5].action = true := by decide
theorem row006 : maskAccessCheck logicalToSuffix (masks 6) program.code[6].action = true := by decide
theorem row007 : maskAccessCheck logicalToSuffix (masks 7) program.code[7].action = true := by decide
theorem row008 : maskAccessCheck logicalToSuffix (masks 8) program.code[8].action = true := by decide
theorem row009 : maskAccessCheck logicalToSuffix (masks 9) program.code[9].action = true := by decide

end Shared.Beeping.NPcoNP.Parent290OwnershipShard00
