import Shared.Beeping.NPcoNP.CoalescingMaskCheck
import Shared.Beeping.NPcoNP.Coalescing284Map
import Shared.Beeping.NPcoNP.Parent290MaskData

/-! Kernel ownership checks for generated program rows 180–184.
External source and physical bindings remain unproved. -/
namespace Shared.Beeping.NPcoNP.Parent290OwnershipShard18
open CoalescingAlgebra Coalescing284Map Parent290MaskData
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem row180 : maskAccessCheck logicalToSuffix (masks 180) program.code[180].action = true := by decide
theorem row181 : maskAccessCheck logicalToSuffix (masks 181) program.code[181].action = true := by decide
theorem row182 : maskAccessCheck logicalToSuffix (masks 182) program.code[182].action = true := by decide
theorem row183 : maskAccessCheck logicalToSuffix (masks 183) program.code[183].action = true := by decide
theorem row184 : maskAccessCheck logicalToSuffix (masks 184) program.code[184].action = true := by decide

end Shared.Beeping.NPcoNP.Parent290OwnershipShard18
