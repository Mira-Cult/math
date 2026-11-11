import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S219C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21437)) 459538477 459571245 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 459538477 459571245).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21437 459538477 459571245
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21438)) 459571245 459604013 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 459571245 459604013).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21438 459571245 459604013
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21439)) 459604013 459636781 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 459604013 459636781).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21439 459604013 459636781
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21439)) 459636781 459669549 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 459636781 459669549).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21439 459636781 459669549
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 459538477 459604013).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 459538477 ≤ 459571245)
    (by decide : 459571245 ≤ 459604013) block0 block1

theorem join_0_1 : (twinPrimeSegment 459604013 459669549).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 459604013 ≤ 459636781)
    (by decide : 459636781 ≤ 459669549) block2 block3

theorem join_1_0 : (twinPrimeSegment 459538477 459669549).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 459538477 ≤ 459604013)
    (by decide : 459604013 ≤ 459669549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 459538477 459669549).card = 440 := join_1_0

end S219C02
end Sude.GeneratedTwinScan
