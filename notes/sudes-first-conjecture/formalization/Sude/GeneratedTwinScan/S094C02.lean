import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S094C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14050)) 197394477 197427245 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 197394477 197427245).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14050 197394477 197427245
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14052)) 197427245 197460013 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 197427245 197460013).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14052 197427245 197460013
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14053)) 197460013 197492781 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 197460013 197492781).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14053 197460013 197492781
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14054)) 197492781 197525549 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 197492781 197525549).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14054 197492781 197525549
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 197394477 197460013).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 197394477 ≤ 197427245)
    (by decide : 197427245 ≤ 197460013) block0 block1

theorem join_0_1 : (twinPrimeSegment 197460013 197525549).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 197460013 ≤ 197492781)
    (by decide : 197492781 ≤ 197525549) block2 block3

theorem join_1_0 : (twinPrimeSegment 197394477 197525549).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 197394477 ≤ 197460013)
    (by decide : 197460013 ≤ 197525549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 197394477 197525549).card = 466 := join_1_0

end S094C02
end Sude.GeneratedTwinScan
