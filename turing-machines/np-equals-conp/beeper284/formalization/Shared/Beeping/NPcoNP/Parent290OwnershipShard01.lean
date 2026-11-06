import Shared.Beeping.NPcoNP.CoalescingMaskCheck
import Shared.Beeping.NPcoNP.Coalescing284Map
import Shared.Beeping.NPcoNP.Parent290MaskData

/-! Kernel ownership checks for generated program rows 10–19.
External source and physical bindings remain unproved. -/
namespace Shared.Beeping.NPcoNP.Parent290OwnershipShard01
open CoalescingAlgebra Coalescing284Map Parent290MaskData
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem row010 : maskAccessCheck logicalToSuffix (masks 10) program.code[10].action = true := by decide
theorem row011 : maskAccessCheck logicalToSuffix (masks 11) program.code[11].action = true := by decide
theorem row012 : maskAccessCheck logicalToSuffix (masks 12) program.code[12].action = true := by decide
theorem row013 : maskAccessCheck logicalToSuffix (masks 13) program.code[13].action = true := by decide
theorem row014 : maskAccessCheck logicalToSuffix (masks 14) program.code[14].action = true := by decide
theorem row015 : maskAccessCheck logicalToSuffix (masks 15) program.code[15].action = true := by decide
theorem row016 : maskAccessCheck logicalToSuffix (masks 16) program.code[16].action = true := by decide
theorem row017 : maskAccessCheck logicalToSuffix (masks 17) program.code[17].action = true := by decide
theorem row018 : maskAccessCheck logicalToSuffix (masks 18) program.code[18].action = true := by decide
theorem row019 : maskAccessCheck logicalToSuffix (masks 19) program.code[19].action = true := by decide

end Shared.Beeping.NPcoNP.Parent290OwnershipShard01
