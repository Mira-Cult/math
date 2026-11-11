import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S171C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18951)) 359137325 359170093 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 359137325 359170093).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18951 359137325 359170093
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18952)) 359170093 359202861 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 359170093 359202861).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18952 359170093 359202861
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18953)) 359202861 359235629 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 359202861 359235629).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18953 359202861 359235629
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18954)) 359235629 359268397 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 359235629 359268397).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18954 359235629 359268397
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 359137325 359202861).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 359137325 ≤ 359170093)
    (by decide : 359170093 ≤ 359202861) block0 block1

theorem join_0_1 : (twinPrimeSegment 359202861 359268397).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 359202861 ≤ 359235629)
    (by decide : 359235629 ≤ 359268397) block2 block3

theorem join_1_0 : (twinPrimeSegment 359137325 359268397).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 359137325 ≤ 359202861)
    (by decide : 359202861 ≤ 359268397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 359137325 359268397).card = 462 := join_1_0

end S171C04
end Sude.GeneratedTwinScan
