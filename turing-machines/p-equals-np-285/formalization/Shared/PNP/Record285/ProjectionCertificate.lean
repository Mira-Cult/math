import Shared.PNP.Record285.RegisterProjection
import Shared.PNP.Record285.ProjectionData

set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.OwnershipCore

/-- The producer retained slots 0--7 and 11 onward, deleting 8--10. -/
def lift (i : Nat) : Nat := if i < 8 then i else i+3

theorem lift_injective : Function.Injective lift := by
  intro a b h
  by_cases ha : a < 8 <;> by_cases hb : b < 8 <;> simp [lift,ha,hb] at h <;> omega

theorem omitted_not_in_image (k : Nat) (hk : k = 8 ∨ k = 9 ∨ k = 10) :
    ∀ j, lift j ≠ k := by
  intro j
  by_cases hj : j < 8 <;> simp [lift,hj] <;> omega

theorem projection_checked : check lift originalRows expandedRows = true := by decide

end Shared.PNP.Record285.RegisterProjection
