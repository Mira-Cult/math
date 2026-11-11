import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S146C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17555)) 308150317 308183085 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 308150317 308183085).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17555 308150317 308183085
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17556)) 308183085 308215853 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 308183085 308215853).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17556 308183085 308215853
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17557)) 308215853 308248621 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 308215853 308248621).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17557 308215853 308248621
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17557)) 308248621 308281389 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 308248621 308281389).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17557 308248621 308281389
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 308150317 308215853).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 308150317 ≤ 308183085)
    (by decide : 308183085 ≤ 308215853) block0 block1

theorem join_0_1 : (twinPrimeSegment 308215853 308281389).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 308215853 ≤ 308248621)
    (by decide : 308248621 ≤ 308281389) block2 block3

theorem join_1_0 : (twinPrimeSegment 308150317 308281389).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 308150317 ≤ 308215853)
    (by decide : 308215853 ≤ 308281389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 308150317 308281389).card = 451 := join_1_0

end S146C15
end Sude.GeneratedTwinScan
