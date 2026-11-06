import Shared.Beeping.NPcoNP.CoalescingMaskCheck
import Shared.Beeping.NPcoNP.Coalescing284Map
import Shared.Beeping.NPcoNP.Parent290MaskData

/-! Kernel ownership checks for generated program rows 80–89.
External source and physical bindings remain unproved. -/
namespace Shared.Beeping.NPcoNP.Parent290OwnershipShard08
open CoalescingAlgebra Coalescing284Map Parent290MaskData
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem row080 : maskAccessCheck logicalToSuffix (masks 80) program.code[80].action = true := by decide
theorem row081 : maskAccessCheck logicalToSuffix (masks 81) program.code[81].action = true := by decide
theorem row082 : maskAccessCheck logicalToSuffix (masks 82) program.code[82].action = true := by decide
theorem row083 : maskAccessCheck logicalToSuffix (masks 83) program.code[83].action = true := by decide
theorem row084 : maskAccessCheck logicalToSuffix (masks 84) program.code[84].action = true := by decide
theorem row085 : maskAccessCheck logicalToSuffix (masks 85) program.code[85].action = true := by decide
theorem row086 : maskAccessCheck logicalToSuffix (masks 86) program.code[86].action = true := by decide
theorem row087 : maskAccessCheck logicalToSuffix (masks 87) program.code[87].action = true := by decide
theorem row088 : maskAccessCheck logicalToSuffix (masks 88) program.code[88].action = true := by decide
theorem row089 : maskAccessCheck logicalToSuffix (masks 89) program.code[89].action = true := by decide

end Shared.Beeping.NPcoNP.Parent290OwnershipShard08
